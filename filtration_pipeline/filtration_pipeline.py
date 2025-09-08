import os 
import pandas as pd
from typing import List, Dict, Any, Optional
from LLM_provider import OpenAIProvider, AnthropicProvider 
from Concurrency import Concurrency
from duplicate_finder import DuplicateFinder
from helpers import read_file, extract_dafny_code, load_prompts
from automated_count import find_noncommented_statement_indices, num_methods_ensures
import random
from enum import Enum


class FilterType(str, Enum):
    one = "easyness"
    two = "understandable"
    three = "fully_specified"

class FiltrationPipeline:
    """
    Main pipeline for processing Dafny files through various filtering and analysis steps
    """
    
    def __init__(self, 
                 run_num: int,
                 max_workers: int = 10,
                 anthro_model: str = "claude-sonnet-4-20250514", 
                 open_model: str = "gpt-4",
                 prompts_path: str = "prompts.yaml", 
                 root_dir: str = "./DafnyBench/DafnyBench/dataset/body_removed",
                 starting_xlsx: str = None, 
                 mode: str = None) -> None:
        """
        Initialize the pipeline with providers and configuration
        
        Args:
            run_num: Run number for this pipeline instance
            max_workers: Number of concurrent workers
            anthro_model: Anthropic model to use
            open_model: OpenAI model to use
            prompts_path: Path to prompts configuration file
        """

        #LLM providers and helpers
        self.anthro_provider = AnthropicProvider()
        self.open_provider = OpenAIProvider()
        self.concurrency = Concurrency(self.anthro_provider, self.open_provider, max_workers)
        self.anthro_model = anthro_model
        self.open_model = open_model
        self.prompts = load_prompts(prompts_path)

        self.max_workers = max_workers
        
        
        if mode == "evaluate_pipeline":
            self.evaluate_pipeline = True
            self.debug_num = 50 # when evaluating the pipeline we want all files
        else:
            self.debug_num = 10
            self.evaluate_pipeline = False
        
        # Results storage
        self.results = {}
        self.run_num = run_num
        self.results_dir = "./run_" + str(self.run_num) + "/results"
        os.makedirs(self.results_dir, exist_ok=True)        
        self.manual_check_dir = "./run_" + str(self.run_num) + "/manual_check"
        os.makedirs(self.manual_check_dir, exist_ok=True)   
        self.summary_text = "./run_" + str(self.run_num) + "/summary.txt"
        with open(self.summary_text, "a") as f:
            f.write(" /\\_/\\\n( o.o )\n > ^ <\n" + "Pipeline initialized!\nRun Number: " + str(self.run_num) + "\n\n")
        self.summary_results = "./run_" + str(self.run_num) + "/results_summary.xlsx"
        # creation of the spreadsheet is under step_zero_make_first_spreadsheet

        # New files storage
        self.root_dir = root_dir
        self.filtered_dir = "./run_"  + str(self.run_num) + "/new_filtered"
        os.makedirs(self.filtered_dir, exist_ok=True)
        self.tests_dir = "./run_" + str(self.run_num) + "/new_tests"
        os.makedirs(self.tests_dir, exist_ok=True)

        #initialize naming and steps
        self.steps_run = 0 
        self.files = []
        self.default_names = ["filter", "count", "duplicates", "unify", "tests"]

        #make first spreadsheet
        if starting_xlsx is not None:
            if os.path.exists(os.path.join(self.results_dir, starting_xlsx)):
                self.files.append(starting_xlsx)
                print(f"Using existing spreadsheet: {starting_xlsx}")
                self.steps_run = int(starting_xlsx[0]) + 1
            else:
                print("entered starting file " + starting_xlsx + " does not exist")
                self.step_zero_make_first_spreadsheet(mode = mode)
        else:
            self.step_zero_make_first_spreadsheet(mode = mode)
    
    def update_summary(self, data, step_name) -> None:
        summary_data = pd.read_excel(self.summary_results)
        for i in range(len(data["filepath"])):
            if data["keepToss"][i] == "TOSS":
                filename = os.path.basename(data["filepath"][i])
                all_filenames = summary_data["filename"].tolist()
                try:
                    idx1 = all_filenames.index(filename)
                except ValueError:
                    idx1 = -1
                try:
                    idx2 = all_filenames.index(filename.split("_", 1)[1])
                except ValueError:
                    idx2 = -1

                index = max(idx1, idx2)
                if index > -1: 
                    summary_data["keepToss"][index] = "TOSS"
                    summary_data["tossedAt"][index] = step_name
                    if "reasoning" in data.keys():
                        summary_data["reasoning"][index] = data["reasoning"][i]
        
        df_summary = pd.DataFrame(summary_data)
        df_summary.to_excel(self.summary_results, sheet_name='Sheet1', index=False)
        print(f"Summary results saved to {self.summary_results}")
        
    def manual_check(self, output_file: str,  kept: int = 15, tossed: int = 15) -> None:
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
        step_filepath = os.path.join(self.results_dir, output_file + ".xlsx")
        step_results = pd.read_excel(step_filepath)

        kept_indices = []
        tossed_indices = []

        # finds the files that were kept and tossed 
        for i, val in enumerate(step_results["keepToss"]):
            if val == "KEEP":
                kept_indices.append(i)
            elif val == "TOSS":
                tossed_indices.append(i)
        
        text_output = "===== Step: "+ output_file + "  ====="
        text_output = text_output + "\nKept total: " + str(len(kept_indices)) + "\nTossed total: " + str(len(tossed_indices)) + "\n" 
        text_output += "Input file: " + self.files[-1]
        text_output += "\nResults saved to " + step_filepath + "\n\n"

        # store and print kept and tossed 
        print(text_output)
        with open(self.summary_text, "a") as f:
            f.write(text_output)

        # samples randomly from the kept and tossed files
        kept = min(kept, len(kept_indices))
        tossed = min(tossed, len(tossed_indices))

        random_kept = random.sample(kept_indices, kept)
        random_tossed = random.sample(tossed_indices, tossed)

        print(kept)
        
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
        filename = output_file + "_manual_check.dfy"
        filepath = os.path.join(self.manual_check_dir, filename)

        with open(filepath, 'w') as f:
            f.write(manual_check_output)
        
    def save_data(self, data: Dict[str, Any], output_file: str, debug: bool = False) -> None:
        """
        Save data to an Excel file
        
        Args:
            data: Dictionary containing data to save
            output_file: Output file path
        """
        self.update_summary(data, output_file)

        df_result = pd.DataFrame(data)
        output_file_path = os.path.join(self.results_dir, output_file + ".xlsx")
        df_result.to_excel(output_file_path, sheet_name='Sheet1', index=False)
        print(f"Results saved to {output_file_path}")
        
        if debug:
            self.manual_check(output_file, kept = self.debug_num, tossed = self.debug_num)
        else:
            self.manual_check(output_file)

        self.steps_run += 1
        self.files.append(output_file + ".xlsx")

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

    def compare_results(self,
                        input_file: str = None):
        human_verified = "./filtration_pipeline/human_verified_sample.xlsx"
        
        if input_file is None: 
            input_file: str = self.files[-1]
        input_file_path = os.path.join(self.results_dir, input_file) 

        human_verified_read = pd.read_excel(human_verified)
        input_file_read = pd.read_excel(input_file_path)

        output = {
            "filename": [],
            "filepath": [],
            "human_decision": [],
            "disagreement": [],
        }
        for key in input_file_read.keys():
            if key not in output:
                output[key] = []
        disagreements = 0
        human_keep = 0 
        human_toss = 0 

        #creates a spreadsheet showing the human output vs the LLM output. 
        for i in range(len(human_verified_read["filename"])):
            filename = human_verified_read["filename"][i]
            human_decision = human_verified_read["keepToss"][i]
            index = next((j for j, name in enumerate(input_file_read["filename"]) if name == filename), None)
            if index is not None:
                llm_decision = input_file_read["keepToss"][index]
                for key in input_file_read.keys():
                    output[key].append(input_file_read[key][index])
            else:
                for key in input_file_read.keys():
                    if key == "filename":
                        output[key].append(filename)
                    elif key == "filepath":
                        output[key].append(human_verified_read["filepath"][i])
                    else:
                        output[key].append("")
                llm_decision = "TOSS"
            output["human_decision"].append(human_decision)
            if llm_decision != human_decision:
                disagreements += 1
                if human_decision == "KEEP":
                    human_keep += 1
                elif human_decision == "TOSS":
                    human_toss += 1
                output["disagreement"].append("DISAGREE")
            else:
                output["disagreement"].append("AGREE")
            
        df_result = pd.DataFrame(output)
        output_file = "compare_" + input_file
        output_file_path = os.path.join(self.results_dir, output_file)
        df_result.to_excel(output_file_path, sheet_name='Sheet1', index=False)

        results_print = "===== Comparison Results =====\nDisagreements: " + str(disagreements) + "\nDisagreement, Human Keep LLM Toss: " + str(human_keep) + "\nDisagreement, Human Toss LLM Keep: " + str(human_toss)+ "\nResults saved to " + output_file_path + "\n\n"
        print(results_print)
        with open(self.summary_text, "a") as f:
            f.write(results_print)

    def step_zero_make_first_spreadsheet(self,
                                         mode: Optional[str] = None):
        """
        makes a spreadsheet of initial files with all marked as KEEP
        >> allows the pipeline to start from any step 
        """
        output_file = "initial_spreadsheet"
        output = {
            "filepath": [],
            "keepToss": []
        }

        summary_data = {
            "filepath": [],
            "filename": [],
            "keepToss": [],
            "tossedAt": [],
            "reasoning": [],
        }

        if mode is None:
            for root, dirs, files in os.walk(self.root_dir):
                for file in files:
                    if file.endswith('.dfy'):
                        output["filepath"].append(os.path.join(root, file))
                        output["keepToss"].append("KEEP")
                        summary_data["filename"].append(file)
                        summary_data["filepath"].append(os.path.join(root, file))
                        summary_data["keepToss"].append("KEEP")
                    
        elif mode == "evaluate_pipeline":
            human_verified = "./filtration_pipeline/human_verified_sample.xlsx"
            human = pd.read_excel(human_verified)
            for filepath in human["filepath"]:
                output["filepath"].append(filepath)
                output["keepToss"].append("KEEP")
                summary_data["filename"].append(os.path.basename(filepath))
                summary_data["filepath"].append(filepath)
                summary_data["keepToss"].append("KEEP")
        else:
            raise ValueError("mode must be None or 'evaluate_pipeline'")

        summary_data["tossedAt"] = ["NA" for i in range(len(summary_data["filepath"]))]
        summary_data["reasoning"] = ["NA" for i in range(len(summary_data["filepath"]))]

        df_result = pd.DataFrame(output)
        output_filepath = os.path.join(self.results_dir, "0_"+ output_file + ".xlsx")
        df_result.to_excel(output_filepath, sheet_name='Sheet1', index=False)

        text_output = "===== Step: step_zero =====\nInitial number of files to process: " + str(len(output["filepath"])) + "\nResults saved to 0_s0_initial_spreadsheet.xlsx\n\n" 
        print(text_output)
        with open(self.summary_text, "a") as f:
            f.write(text_output)
        self.files.append("0_" + output_file + ".xlsx")
        self.steps_run += 1

        if not os.path.exists(self.summary_results):
            df_summary = pd.DataFrame(summary_data)
            df_summary.to_excel(self.summary_results, sheet_name='Sheet1', index=False)
            print(f"Summary results saved to {self.summary_results}")
    
    def filter(self, 
                        test: FilterType,
                        debug: bool = False) -> Dict[str, List]:
        """
        Step 1: filter files based on test
        
        Args:
            test: FilterType enum value representing the filtering test to apply
            debug: If True, limit the number of files processed for debugging

        Returns:
            Dictionary with filtering results
        """

        cur_test = test.value if isinstance(test, FilterType) else test

        input_file: str = self.files[-1]
        output_file: str = str(self.steps_run) + "_" + cur_test + "_"+ self.default_names[0]
        print(output_file)

        file_paths = self.get_filepaths(input_file, debug=debug)
                
        print(f"Processing {len(file_paths)} files for filtering...")
        
        # Prepare prompts
        system_prompt = self.prompts[cur_test]["overall_goal"]
        message_prompt = (self.prompts[cur_test]["task"] + 
                          self.prompts[cur_test]["examples"] + 
                         self.prompts[cur_test]["output_request"] + 
                         self.prompts[cur_test]["file"])
        
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
        self.save_data(results, output_file, debug=debug)

        if self.evaluate_pipeline: 
            self.compare_results()

        return results

    def step_one_run_full(self, 
                    debug: bool = False) -> Dict[str, List]:
        self.filter(FilterType.one, debug=debug)
        self.filter(FilterType.two)
        self.filter(FilterType.three)

    
    def sanity_check(self, 
                                debug: bool = False) -> Dict[str, List]:
        """
        Step 3: Sanity check
        
        Args:
            input_file: Input Excel file from step three
            output_file: Output Excel file path
            
        Creates:
            spreadsheet with a manual count of the number of functions/methods/lemmas missing ensures/requires statements for each function
        """
        input_file: str = self.files[-1]
        output_file: str = str(self.steps_run) + "_"+ self.default_names[1]

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
        
        self.save_data(data, output_file, debug=debug)

        if self.evaluate_pipeline: 
            self.compare_results()

        return data

    def unify_format(self, 
                               debug: bool = False) -> Dict[str, List]:
        input_file: str = self.files[-1]
        output_file: str = str(self.steps_run) + "_" + self.default_names[3]

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
            max_tokens=8000,
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
        
        self.save_data(results, output_file, debug=debug)
    
    def delete_duplicates(self,
                                    debug: bool = False, 
                                    bound: int = 0.9) -> Dict[str, List]:
        """
        Removes duplicates from the results of step three, ensuring that for each type of program (ie. binary search) there is only one file kept

        Arg:
            bound: float between 0 and 1 representing the cosine similarity threshold for considering files as duplicates.
        """
        input_file: str = self.files[-1]
        output_file: str = str(self.steps_run) + "_" +self.default_names[2] 

        file_paths = self.get_filepaths(input_file, debug=debug)

        duplicate_finder = DuplicateFinder(file_paths, input_file, output_file + ".xlsx", self.concurrency, self.results_dir, bound = bound)

        duplicate_finder.run()

        self.files.append(output_file + ".xlsx")

        # output_filepath = os.path.join(self.results_dir, output_file)
        if debug:
            self.manual_check(output_file, kept = self.debug_num, tossed = self.debug_num)
        else:
            self.manual_check(output_file)

        self.steps_run += 1
    
    def create_tests(self, 
                               debug: bool = False) -> Dict[str, List]:
        
        input_file: str = self.files[-1]
        output_file: str = str(self.steps_run) + "_"+ self.default_names[4]

        file_paths = self.get_filepaths(input_file, debug=debug)

        system_prompt = self.prompts["write_tests"]["overall_goal"]
        message_prompt = self.prompts["write_tests"]["examples"] + self.prompts["write_tests"]["output_request"] + self.prompts["write_tests"]["file"] 

        responses = self.concurrency.send_messages_with_progress(
            system_prompt=system_prompt,
            message_prompt=message_prompt,
            inputs=file_paths,
            provider="anthro",
            input_type="filepaths",
            max_tokens=3000,
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
        
        self.save_data(results, output_file, debug=debug)

    # def summarize_filtration(self):

    #     data = {
    #         "filepath": [],
    #         "keepToss": [],
    #         "tossedAt": [],
    #     }

    #     initial_filepath = os.path.join(self.results_dir, "0_initial_spreadsheet.xlsx")
    #     initial_data = pd.read_excel(initial_filepath)

    #     for file in initial_data["filepath"]:
    #         data["filepath"].append(file)
    #         data["keepToss"].append("KEEP") 
    #         data["tossedAt"].append("NA")
        
    #     for entry in os.listdir(self.results_dir): 
    #         filepath = os.path.join(self.results_dir, entry)
    #         if os.path.isfile(filepath) and entry.endswith(".xlsx"):
    #             step_data = pd.read_excel(filepath)
    #             for i in range(len(step_data["keepToss"])):
    #                 filepath = step_data["filepath"][i]
    #                 if step_data["keepToss"][i] == "TOSS":
    #                     index = data["filepath"].index(filepath)
    #                     data["keepToss"][index] = "TOSS"
    #                     data["tossedAt"][index] = entry
        
    #     output_filepath = os.path.join(self.results_dir, "summary_filtration.xlsx")
    #     df_result = pd.DataFrame(data)
    #     df_result.to_excel(output_filepath, sheet_name='Sheet1', index=False)


    def repeated_step_run(self, step: int, num_runs: int, num_majority: int, debug: bool = False) -> None:
        """
        Run a step run and take the majority Keep/Toss decision for each. 
        """
        if step == 1: 
            method = self.step_one_filter_layer_1
        elif step == 2:
            method = self.step_two_filter_layer_2
        else:
            raise ValueError("step must be 1 or 2")

        all_results = {
            "keepToss": [],
        }
        for i in range(num_runs):
            cur_result = method(debug = debug, save_data = False)
            for key in cur_result.keys():
                if key != "filename" and key != "filepath":
                    new_key = str(i) + "_" + key
                    all_results[new_key] = cur_result[key]
                else:
                    all_results[key] = cur_result[key]
        
        for i in range(len(all_results["filename"])):
            keep_count = 0
            toss_count = 0
            for j in range(num_runs):
                decision = all_results[str(j) + "_keepToss"][i]
                if decision == "KEEP":
                    keep_count += 1
                elif decision == "TOSS":
                    toss_count += 1
    
            if keep_count >= num_majority:
                final_decision = "KEEP"
            else:
                final_decision = "TOSS"

            all_results["keepToss"].append(final_decision)
    
        self.save_data(all_results, str(self.steps_run) + "r" + str(num_runs) +  "_"+ self.default_names[step-1], debug=debug)
    
    def run_full_pipeline(self):
        self.sanity_check()
        self.filter(FilterType.one)
        while True:
            choice = input("Do you want to keep going? (y/n): ").strip().lower()
            if choice == "n":
                print("Exiting program.")
                break
            elif choice == "y":
                continue
            else:
                print("Invalid input, please enter 'y' or 'n'.")
        self.filter(FilterType.two)
        self.unify_format()
        while True:
            choice = input("Do you want to keep going? (y/n): ").strip().lower()
            if choice == "n":
                print("Exiting program.")
                break
            elif choice == "y":
                continue
            else:
                print("Invalid input, please enter 'y' or 'n'.")
        self.delete_duplicates()
        while True:
            choice = input("Do you want to keep going? (y/n): ").strip().lower()
            if choice == "n":
                print("Exiting program.")
                break
            elif choice == "y":
                continue
            else:
                print("Invalid input, please enter 'y' or 'n'.")
        self.create_tests()