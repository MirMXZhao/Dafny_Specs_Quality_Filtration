import os 
import pandas as pd
from typing import List, Dict, Any, Optional
from LLM_provider import OpenAIProvider, AnthropicProvider 
from Concurrency import Concurrency
from DuplicateFinder import DuplicateFinder
from helpers import read_file, extract_dafny_code, load_prompts
from automated_count import find_noncommented_statement_indices, num_methods_ensures
import random

class Pipeline:
    """
    Main pipeline for processing Dafny files through various filtering and analysis steps
    """
    
    def __init__(self, 
                 max_workers: int = 10,
                 anthro_model: str = "claude-sonnet-4-20250514", 
                 open_model: str = "gpt-4",
                 prompts_path: str = "prompts.yaml"):
        """
        Initialize the pipeline with providers and configuration
        
        Args:
            max_workers: Number of concurrent workers
            anthro_model: Anthropic model to use
            open_model: OpenAI model to use
            prompts_path: Path to prompts configuration file
        """
        self.anthro_provider = AnthropicProvider()
        self.open_provider = OpenAIProvider()
        self.concurrency = Concurrency(self.anthro_provider, self.open_provider, max_workers)
        self.anthro_model = anthro_model
        self.open_model = open_model
        self.prompts = load_prompts(prompts_path)
        self.max_workers = max_workers
        
        # Results storage
        self.results_dir = "./filtration_pipeline/results"
        os.makedirs(self.results_dir, exist_ok=True)
        
        self.manual_check_dir = "./filtration_pipeline/manual_check"

        self.debug_num = 10 # Number of files to process in debug mode

        self.results = {}
    
    def manual_check(self, step: str, kept: int = 15, tossed: int = 15) -> None:
        """
        Outputs kept Kept files and toss Tossed files for manual checking into a file for ease of access. 
        Not part of the pipeline formally, but useful for checking that the LLM is performing well 
        
        Args:
            step: Step name for manual check (ie. "step_one", "step_two", etc.)
            kept: Number of files kept to check
            toss: Number of files tossed to check 

        Creates: 
            A text file with the kept and tossed files for manual checking, along with the descriptions of what the LLM outputted if applicable
        """
        if step not in self.results:
            raise ValueError(f"No results found for step: {step}. Please run the pipeline first.")

        step_filepath = self.results[step]
        step_results = pd.read_excel(step_filepath)

        kept_indices = []
        tossed_indices = []

        for i, val in enumerate(step_results["keepToss"]):
            if val == "KEEP":
                kept_indices.append(i)
            elif val == "TOSS":
                tossed_indices.append(i)

        print("Kept total: ", len(kept_indices))
        print("Tossed total: ", len(tossed_indices))
        
        kept = min(kept, len(kept_indices))
        tossed = min(tossed, len(tossed_indices))

        random_kept = random.sample(kept_indices, kept)
        random_tossed = random.sample(tossed_indices, tossed)
        
        manual_check_arr = []
        for i in range(kept): 
            index = random_kept[i]
            filepath = step_results["filepath"][index]
            manual_check_arr.append(f"// Kept File {i+1}:\n")
            for key in step_results.keys():
                manual_check_arr.append(f"// {key}: {step_results[key][index]}\n")
            with open(filepath, 'r') as file:
                content = file.read()
                manual_check_arr.append(f"\n{content}\n")

        for i in range(tossed): 
            index = random_tossed[i]
            filepath = step_results["filepath"][index]
            manual_check_arr.append(f"// Tossed File {i+1}:\n")
            for key in step_results.keys():
                manual_check_arr.append(f"// {key}: {step_results[key][index]}\n")
            with open(filepath, 'r') as file:
                content = file.read()
                manual_check_arr.append(f"{content}\n\n\n")

        manual_check_output = ''.join(manual_check_arr)
        filename = step + "_manual_check.dfy"
        filepath = os.path.join(self.manual_check_dir, filename)

        with open(filepath, 'w') as f:
            f.write(manual_check_output)
    
    def get_filepaths(self, input_file: str, debug: bool = False):
        input_file_path = os.path.join(self.results_dir, input_file)
        df = pd.read_excel(input_file_path)
        file_paths = [] 
        i = 0
        for index, val in enumerate(df["keepToss"]):
            if val == "KEEP":
                if i < self.debug_num or not debug:
                    file_paths.append(df["filepath"][index])
                    i += 1
        
        return file_paths 
    
    def save_data(self, step_name: str, data: Dict[str, Any], output_file: str, debug: bool = False) -> None:
        """
        Save data to an Excel file
        
        Args:
            data: Dictionary containing data to save
            output_file: Output file path
        """
        df_result = pd.DataFrame(data)
        output_file_path = os.path.join(self.results_dir, output_file)
        df_result.to_excel(output_file_path, sheet_name='Sheet1', index=False)
        print(f"Results saved to {output_file_path}")
        
        self.results[step_name] = output_file_path
        if debug:
            self.manual_check(step_name, kept = 2, tossed = 2)
        else:
            self.manual_check(step_name)

    
    def step_one_filter_layer_1(self, 
                               directory: str = None,
                               output_file: str = "filter_s1.xlsx", debug: bool = False) -> Dict[str, List]:
        """
        Step 1: Filter problems based on 7 criteria that aim to remove problems that aren't clearly understandable are too easy or difficult
        
        Args:
            directory: Directory containing files to process
            output_file: Output Excel file path
            
        Returns:
            Dictionary with filtering results
        """
        if directory is None:
            directory = '/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed'
        
        # Get all file paths
        file_paths = []
        i = 0 
        for root, dirs, files in os.walk(directory):
            for file in files:
                if i < 30 or not debug:
                    if file.endswith('.dfy'):
                        file_paths.append(os.path.join(root, file))
                        i += 1
        
        print(f"Processing {len(file_paths)} files for filtering...")
        
        # Prepare prompts
        system_prompt = self.prompts["filter_problems"]["overall_goal"]
        message_prompt = (self.prompts["filter_problems"]["task"] + 
                         self.prompts["filter_problems"]["output_request"] + 
                         self.prompts["filter_problems"]["file"])
        
        # Process files with progress tracking
        responses = self.concurrency.send_messages_with_progress(
            system_prompt=system_prompt,
            message_prompt=message_prompt,
            inputs=file_paths,
            provider="anthro",
            input_type="filepaths",
            max_tokens=500,
            model=self.anthro_model,
            progress_interval=10
        )
        
        # Parse responses
        results = {
            "filename": [],
            "filepath": [],
            "keepToss": [],
            "violated": [],
            "reasoning": []
        }
        
        for i, (filepath, response) in enumerate(zip(file_paths, responses)):
            filename = os.path.basename(filepath)
            results["filename"].append(filename)
            results["filepath"].append(filepath)
            
            if response.startswith("ERROR"):
                results["keepToss"].append("ERROR")
                results["violated"].append("ERROR")
                results["reasoning"].append(response)
            else:
                try:
                    lines = response.splitlines()
                    if len(lines) >= 3:
                        results["keepToss"].append(lines[0])
                        results["violated"].append(lines[1])
                        results["reasoning"].append(lines[2])
                    else:
                        results["keepTrash"].append("PARSE_ERROR")
                        results["violated"].append("PARSE_ERROR")
                        results["reasoning"].append(response)
                except Exception as e:
                    results["keepTrash"].append("PARSE_ERROR")
                    results["violated"].append("PARSE_ERROR")
                    results["reasoning"].append(f"Parse error: {e}")
        
        # Save results
        self.save_data("step_one", results, output_file, debug=debug)

        return results
    
    def step_two_filter_layer_2(self, 
                                 input_file: str = "filter_s1.xlsx",
                                 output_file: str = "filter_s2.xlsx",
                                 debug: bool = False) -> Dict[str, List]:
        """
        Step 3: Second layer of filtering
        
        Args:
            input_file: Input Excel file from step one
            output_file: Output Excel file path
            
        Returns:
            Dictionary with layer 2 filtering results
        """
        if input_file is None:
            input_file = os.path.basename(self.results["step_one"])

        file_paths = self.get_filepaths(input_file, debug=debug)
                
        print(f"Processing {len(file_paths)} files for filtering...")
        
        # Prepare prompts
        system_prompt = self.prompts["filter_problems_2"]["overall_goal"]
        message_prompt = (self.prompts["filter_problems_2"]["task"] + 
                         self.prompts["filter_problems_2"]["output_request"] + 
                         self.prompts["filter_problems_2"]["file"])
        
        # Process files with progress tracking
        responses = self.concurrency.send_messages_with_progress(
            system_prompt=system_prompt,
            message_prompt=message_prompt,
            inputs=file_paths,
            provider="anthro",
            input_type="filepaths",
            max_tokens=500,
            model=self.anthro_model,
            progress_interval=10
        )
        
        # Parse responses
        results = {
            "filename": [],
            "filepath": [],
            "keepToss": [],
            "reasoning": []
        }
        
        for i, (filepath, response) in enumerate(zip(file_paths, responses)):
            filename = os.path.basename(filepath)
            results["filename"].append(filename)
            results["filepath"].append(filepath)
            
            if response.startswith("ERROR"):
                results["keepToss"].append("ERROR")
                results["reasoning"].append(response)
            else:
                try:
                    lines = response.splitlines()
                    if len(lines) >= 2:
                        results["keepToss"].append(lines[0])
                        results["reasoning"].append(lines[1])
                    else:
                        results["keepTrash"].append("PARSE_ERROR")
                        results["reasoning"].append(response)
                except Exception as e:
                    results["keepTrash"].append("PARSE_ERROR")
                    results["reasoning"].append(f"Parse error: {e}")
        
        # Save results
        self.save_data("step_two", results, output_file, debug=debug)

        return results
    
    def step_three_sanity_check(self, 
                                input_file: str = "filter_s2.xlsx",
                                output_file: str = "count_s3.xlsx", 
                                debug: bool = False) -> Dict[str, List]:
        """
        Step 3: Sanity check
        
        Args:
            input_file: Input Excel file from step three
            output_file: Output Excel file path
            
        Creates:
            spreadsheet with a manual count of the number of functions/methods/lemmas missing ensures/requires statements for each function
        """
        if input_file is None:
            input_file = os.path.basename(self.results["step_two"])

        data = {
            "filename": [],
            "filepath":[],
            "num_methods": [],
            "num_lemmas": [],
            "num_classes": [],
            "num_functions": [],
            "num_predicates": [],
            "num_ensures": [],
            "num_requires": [],
            "num_lines": [],
            "num_no_ensures": [],
            "num_no_requires": [],
            "num_none_either": [],
            "keepToss": [],
        }

        file_paths = self.get_filepaths(input_file, debug=debug)

        for i in range(len(file_paths)):
            filepath = file_paths[i]
            data["filepath"].append(filepath)
            filename = os.path.basename(filepath)
            data["filename"].append(filename)
            with open(filepath, 'r') as file:
                content = file.read()
            count = num_methods_ensures(content)
            for key in count.keys():
                data[key].append(count[key])
            if data["num_no_ensures"][i] > 5 or data["num_methods"][i] + data["num_lemmas"][i] + data["num_functions"][i] + data["num_predicates"][i] > 20:
                data["keepToss"].append("TOSS")
            else:
                data["keepToss"].append("KEEP")
        
        self.save_data("step_three", data, output_file, debug=debug)

        return data
    
    def step_four_delete_duplicates(self,
                                    input_file: str = "count_s3.xlsx",
                                    output_file: str = "duplicates_s4.xlsx",
                                    debug: bool = False) -> Dict[str, List]:
        file_paths = self.get_filepaths(input_file, debug=debug)

        duplicate_finder = DuplicateFinder(file_paths, input_file, output_file, self.concurrency, 0.85)

        duplicate_finder.run()

        step_name = "step_four"
        self.results[step_name] = os.path.join(self.results_dir, output_file)
        if debug:
            self.manual_check(step_name, kept = 2, tossed = 2)
        else:
            self.manual_check(step_name)
    
    def step_five_unify_format(self, 
                               input_file: str = "duplicates_s4.xlsx",
                               output_file: str = "final_results.xlsx",
                               debug: bool = False) -> Dict[str, List]:
        a = 2
    
    def run_full_pipeline(self, 
                         output_dir: str = "./results",
                         save_intermediate: bool = True) -> Dict[str, Any]:
        """
        Run the complete pipeline
        
        Args:
            output_dir: Directory to save results
            save_intermediate: Whether to save intermediate results
            
        Returns:
            Dictionary with all pipeline results
        """
        os.makedirs(output_dir, exist_ok=True)
        
        print("Starting full pipeline...")
        
        # Step 1
        print("\n=== Step 1: Filter Problems ===")
        step1_results = self.step_one_filter_problems(
            output_file=os.path.join(output_dir, "step1_filter_problems.xlsx")
        )
        
        # Step 2
        print("\n=== Step 2: Sanity Check ===")
        step2_results = self.step_two_sanity_check(
            input_file=os.path.join(output_dir, "step1_filter_problems.xlsx"),
            output_file=os.path.join(output_dir, "step2_sanity_check.xlsx")
        )
        
        # Step 3
        print("\n=== Step 3: Layer 2 Filter ===")
        step3_results = self.step_three_filter_layer_2(
            input_file=os.path.join(output_dir, "step2_sanity_check.xlsx"),
            output_file=os.path.join(output_dir, "step3_filter_layer2.xlsx")
        )
        
        # Step 4
        print("\n=== Step 4: Second Sanity Check ===")
        step4_results = self.step_four_sanity_check_2(
            input_file=os.path.join(output_dir, "step3_filter_layer2.xlsx"),
            output_file=os.path.join(output_dir, "step4_sanity_check2.xlsx")
        )
        
        # Compile final results
        final_results = {
            "step1": step1_results,
            "step2": step2_results,
            "step3": step3_results,
            "step4": step4_results
        }
        
        print(f"\nPipeline completed! Results saved to {output_dir}")
        return final_results