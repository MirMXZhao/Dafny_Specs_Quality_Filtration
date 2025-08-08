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
                 run_num: int,
                 max_workers: int = 10,
                 anthro_model: str = "claude-sonnet-4-20250514", 
                 open_model: str = "gpt-4",
                 prompts_path: str = "prompts.yaml", 
                 root_dir: str = "/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed") -> None:
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
        
        self.debug_num = 10 # Number of files to process in debug mode
        
        # Results storage
        self.results = {}
        self.run_num = run_num
        self.results_dir = "./run_" + str(self.run_num) + "/results"
        os.makedirs(self.results_dir, exist_ok=True)        
        self.manual_check_dir = "./run_" + str(self.run_num) + "/manual_check"
        os.makedirs(self.manual_check_dir, exist_ok=True)   
        self.summary_text = "./run_" + str(self.run_num) + "/summary.txt"
        with open(self.summary_text, "w") as f:
            f.write(" /\\_/\\\n( o.o )\n > ^ <\n" + "Pipeline initialized!\nRun Number: " + str(self.run_num) + "\n\n")
         
        # New files storage
        self.root_dir = root_dir
        self.filtered_dir = os.path.join(os.path.dirname(self.root_dir), "run_" + str(self.run_num) + "/filtered")
        os.makedirs(self.filtered_dir, exist_ok=True)
        self.tests_dir = os.path.join(os.path.dirname(self.root_dir), "run_" + str(self.run_num) + "/tests")
        os.makedirs(self.tests_dir, exist_ok=True)

        self.steps_run = 0 
        self.step_zero_make_first_spreadsheet()

    
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

        # finds the files that were kept and tossed 
        for i, val in enumerate(step_results["keepToss"]):
            if val == "KEEP":
                kept_indices.append(i)
            elif val == "TOSS":
                tossed_indices.append(i)
        
        step_descriptions = {
            "step_one": "Filtering based on initial criteria",
            "step_two": "Second layer of filtering",
            "step_three": "Sanity check for ensures and requires statements",
            "step_four": "Removing duplicates",
            "step_five": "Unifying format",
            "step_six": "Creating tests"
        }
        text_output = "===== Step: "+ step + ": " + step_descriptions[step] + "  ====="
        text_output = text_output + "Kept total: " + str(len(kept_indices)) + "\nTossed total: " + str(len(tossed_indices)) + "\n"

        # store and print kept and tossed 
        print(text_output)
        with open("filename.txt", "a") as f:
            f.write(text_output)

        # samples randomly from the kept and tossed files
        kept = min(kept, len(kept_indices))
        tossed = min(tossed, len(tossed_indices))

        random_kept = random.sample(kept_indices, kept)
        random_tossed = random.sample(tossed_indices, tossed)
        
        # outputs and formats the files 
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

    def get_filepaths(self, input_file: str, debug: bool = False):
        """
        Get file paths marked as KEEP from the input spreadsheet
        """
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
    
    def step_zero_make_first_spreadsheet(self):
        """
        makes a spreadsheet of initial files with all marked as KEEP
        >> allows the pipeline to start from any step 
        """
        output = {
            "filepath": [],
            "keepToss": []
        }
        for root, dirs, files in os.walk(self.root_dir):
            for file in files:
                if file.endswith('.dfy'):
                    output["filepath"].append(os.path.join(root, file))
                    output["keepToss"].append("KEEP")

        df_result = pd.DataFrame(output)
        output_filepath = os.path.join(self.results_dir, "initial_spreadsheet_s0.xlsx")
        df_result.to_excel(output_filepath, sheet_name='Sheet1', index=False)
    
    def step_one_filter_layer_1(self, 
                               input_file: str = "s0_initial_spreadsheet.xlsx",
                               output_file: str = "s1_filter.xlsx", debug: bool = False) -> Dict[str, List]:
        """
        Step 1: Filter problems based on 7 criteria that aim to remove problems that aren't clearly understandable are too easy or difficult
        
        Args:
            directory: Directory containing files to process
            output_file: Output Excel file path
            
        Returns:
            Dictionary with filtering results
        """
        file_paths = self.get_filepaths(input_file, debug=debug)
        
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
                                 input_file: str = "s1_filter.xlsx",
                                 output_file: str = "s2_filter.xlsx",
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
                                input_file: str = "s2_filter.xlsx",
                                output_file: str = "s3_count.xlsx", 
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
                                    input_file: str = "s3_count.xlsx",
                                    output_file: str = "s4_duplicates.xlsx",
                                    debug: bool = False, 
                                    bound: int = 0.9) -> Dict[str, List]:
        """
        Removes duplicates from the results of step three, ensuring that for each type of program (ie. binary search) there is only one file kept

        """
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
                               input_file: str = "s4_duplicates.xlsx",
                               output_file: str = "s5_unify.xlsx",
                               debug: bool = False) -> Dict[str, List]:
        if input_file is None:
            input_file = os.path.basename(self.results["step_four"])

        file_paths = self.get_filepaths(input_file, debug=debug)

        results = {
            "filename": [],
            "filepath": [],
            "keepToss": [],
        }

        system_prompt = self.prompts["unify_format"]["overall_goal"]
        message_prompt = self.prompts["unify_format"]["example"] + self.prompts["unify_format"]["output_request"] + self.prompts["unify_format"]["file"]

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

        for i, (filepath, response) in enumerate(zip(file_paths, responses)):
            
            results["keepToss"].append("KEEP")
            
            cur_filename = os.path.basename(filepath)
            new_filename = str(i) + "_" + cur_filename
            new_filepath = os.path.join(self.filtered_dir, new_filename)
            results["filename"].append(new_filename)
            results["filepath"].append(new_filepath)
            with open(new_filepath, 'w') as f:
                f.write("\n".join(extract_dafny_code(response)))
        
        self.save_data("step_five", results, output_file, debug=debug)
    
    def step_six_create_tests(self, 
                               input_file: str = "s5_unify.xlsx",
                               output_file: str = "s6_tests.xlsx",
                               debug: bool = False) -> Dict[str, List]:
        if input_file is None:
            input_file = os.path.basename(self.results["step_five"])

        file_paths = self.get_filepaths(input_file, debug=debug)

        system_prompt = self.prompts["write_tests"]["overall_goal"]
        message_prompt = self.prompts["write_tests"]["examples"] + self.prompts["write_tests"]["output_request"] + self.prompts["write_tests"]["file"] 

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

        results = {
            "filename": [],
            "filepath": [],
            "keepToss": [],
        }

        # Create tests directory if it doesn't exist
        os.makedirs(self.tests_dir, exist_ok=True)

        for i, (filepath, test) in enumerate(zip(file_paths, responses)):
            with open(filepath, 'r') as f:
                original_content = f.read()
            
            filename = os.path.basename(filepath)
            new_filepath = os.path.join(self.tests_dir, filename)

            results["filename"].append(filename)
            results["filepath"].append(new_filepath)
            results["keepToss"].append("KEEP")

            # write the contents to a new file
            new_content = original_content + '\n\n////////TESTS////////\n\n' + ("\n".join(extract_dafny_code(test))).strip() + '\n'

            with open(new_filepath, 'w') as f:
                f.write(new_content)
    
    def repeated_run(self, ):
        """
        Run the pipeline multiple times with different run numbers
        """
        for i in range(1, 6):
            print(f"\n=== Running pipeline iteration {i} ===\n")
            self.run_full_pipeline(results_dir=f"./run_{i}/results", manual_check_dir=f"./run_{i}/manual_check")
        
        print("\n=== Pipeline completed for all iterations ===\n")
    def run_full_pipeline(self, 
                          results_dir: str = None,
                          manual_check_dir: str = None) -> None:
        """
        Run the complete pipeline
        """
        steps_subset = [1, 2, 3, 4, 5, 6]
        self.run_subset(steps_subset, results_dir=results_dir, manual_check_dir=manual_check_dir)

    def run_subset(self, steps_subset: List[int], file_names: List[str] = None, results_dir: str = None, manual_check_dir: str = None):
        """
        Run a subset of the pipeline steps

        Arg:
            steps_subset is a list of numbers from 1 to 6 representing which steps to run
        """
        step_names = ["one", "two", "three", "four", "five", "six"]
        possible_names = ["s1_filter.xlsx", "s2_filter.xlsx", "s3_count.xlsx", "s4_duplicates.xlsx", "s5_unify.xlsx", "s6_addtests.xlsx"]

        if file_names is None or len(file_names) != len(steps_subset):
            file_names = []
            for i in steps_subset:
                if i < 1 or i > 6:
                    raise ValueError(f"Invalid step number: {i}. Must be between 1 and 6.")
                file_names.append(possible_names[i-1])
        
        if results_dir is not None: 
            self.results_dir = results_dir
            os.makedirs(self.results_dir, exist_ok=True)
        
        if manual_check_dir is not None:
            self.manual_check_dir = manual_check_dir
            os.makedirs(self.manual_check_dir, exist_ok=True)

        step_methods = [self.step_one_filter_layer_1, self.step_two_filter_layer_2, self.step_three_sanity_check, self.step_four_delete_duplicates, self.step_five_unify_format]

        for i, step in enumerate(steps_subset):
            print(f"\n=== Step {step}: {step_names[step-1]} ===\n")
            method = step_methods[step-1]
            if step == 1:
                method(output_file=file_names[i], debug=False)
            else:
                input_file = possible_names[step-2]
                method(input_file=input_file, output_file=file_names[i], debug=False)
            
            if i == 0: 
                method(input_file="initial_spreadsheet_s0.xlsx", output_file=file_names[i])
            else:
                method(input_file= file_names[i-1], output_file=file_names[i])


