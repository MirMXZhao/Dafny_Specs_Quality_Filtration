import os 
import pandas as pd
from typing import List, Dict, Any, Optional
from LLM_provider import OpenAIProvider, AnthropicProvider 
from Concurrency import Concurrency
from duplicate_finder import DuplicateFinder
from remove_body import remove_body
from helpers import read_file, extract_dafny_code, load_prompts
import random

class RefinementPipeline():
    def __init__(self,
                 run_num: int, 
                 max_workers: int = 10, 
                 debug: bool = False, 
                 anthro_model: str = "claude-sonnet-4-20250514", 
                 open_model: str = "gpt-4",
                 dir: str = "/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/ground_truth", 
                 ):
        
        self.prompts = load_prompts("spec_refinement.yaml")
        self.anthro_provider = AnthropicProvider()
        self.open_provider = OpenAIProvider()
        self.anthro_model = anthro_model
        self.open_model = open_model
        self.concurrency = Concurrency(self.anthro_provider, self.open_provider, max_workers)
        self.debug = debug
        self.debug_num = 3
        self.dirs = [dir]

        self.run_num = run_num
        self.results_dir = "./refine_run_" + str(self.run_num)
        os.makedirs(self.results_dir, exist_ok=True)     
        self.summary_text = "./refine_run_" + str(self.run_num) + "/summary.txt"
        with open(self.summary_text, "a") as f:
            f.write(" /\\_/\\\n( o.o )\n > ^ <\n" + "Pipeline initialized!\nRun Number: " + str(self.run_num) + "\n\n")
    
    def get_file_paths(self):
        input_dir = self.dirs[-1]
        file_paths = []
        for filename in os.listdir(input_dir):
            file_path = os.path.join(input_dir, filename)
            if os.path.isfile(file_path):
                file_paths.append(file_path)
                if self.debug and len(file_paths) >= self.debug_num:
                    break
        return file_paths
    

    def method_name_improvement(self):
        new_dir = os.path.join(self.results_dir, "method_name_improved")
        os.makedirs(new_dir, exist_ok=True)
        message_prompt = self.prompts["method_name_improvement"]["task"] + self.prompts["method_name_improvement"]["output_request"] + self.prompts["method_name_improvement"]["file"]
        system_prompt = "You are a straightforward assistant to a software engineer who does not talk except to answer the task asked."

        filepaths = self.get_file_paths()

        responses = self.concurrency.send_messages_with_progress(
                system_prompt= system_prompt,
                message_prompt=message_prompt,
                inputs=filepaths,
                provider="anthro",
                input_type="filepaths",
                max_tokens=10000,
                model=self.anthro_model,
                progress_interval=10
                )

        for i, (filepath, response) in enumerate(zip(filepaths, responses)):            
            filename = os.path.basename(filepath)
            new_filepath = os.path.join(dir, filename)

            with open(new_filepath, 'w') as f:
                f.write(response)

        self.dirs.append(dir)
    
        new_text = "====== method_name_improvement completed ======\n\n"
        with open(self.summary_text, "a") as f:
            f.write(new_text)
        
        return responses
    
    def spec_feedback(self, filepaths):
        message_prompt = self.prompts["spec_feedback"]["task"] + self.prompts["spec_feedback"]["output_request"] + self.prompts["method_name_improvement"]["file"]
        system_prompt = "You are a straightforward assistant to a software engineer who does not talk except to answer the task asked."

        responses = self.concurrency.send_messages_with_progress(
                system_prompt= system_prompt,
                message_prompt=message_prompt,
                inputs=filepaths,
                provider="anthro",
                input_type="filepaths",
                max_tokens=700,
                model=self.anthro_model,
                progress_interval=10
        )
        
        new_text = "====== spec_feedback completed ======\nfiles completed " + str(len(filepaths)) + "\n\n"
        with open(self.summary_text, "a") as f:
            f.write(new_text)
        
        return responses

    def spec_refinement(self, feedback, filepaths):
        prompts = []
        for f in feedback:
            new_prompt =  self.prompts["spec_refinement"]["task"] + self.prompts["spec_refinement"]["output_request"] + self.prompts["spec_refinement"]["feedback"] + f + self.prompts["spec_refinement"]["file"]
            prompts.append(new_prompt)
        
        system_prompt = "You are a straightforward assistant to a software engineer who does not talk except to answer the task asked."

        responses = self.concurrency.send_messages_with_custom_prompts(
                system_prompt= system_prompt,
                message_prompts=prompts,
                filepaths=filepaths,
                provider="anthro",
                max_tokens=20000,
                model=self.anthro_model,
        )

        new_text = "====== spec_refinement completed ======\nfiles completed " + str(len(filepaths)) + "\n\n"
        with open(self.summary_text, "a") as f:
            f.write(new_text)
    
        return responses

    def verify_passes(self):
        pass

    # def feedback_improvement_loop(self, 
    #                               iterations: int = 1):
    #     dir = os.path.join(self.results_dir, "feedback_refinement_loop")
    #     os.makedirs(dir, exist_ok=True) 

    #     filepaths = self.get_file_paths()
    #     which_files= [val for val in range(len(filepaths))]

    #     for filepath in filepaths:
    #         filename = os.path.basename(filepath)
    #         filename = filename[:-4] if filename.endswith(".dfy") else filename
    #         new_dir = os.path.join(dir, filename)
    #         os.makedirs(new_dir, exist_ok=True)
    #         with open(filepath, "r") as file:
    #             original_text = file.read()
    #         with open(os.path.join(new_dir, "0_original.dfy"), "w") as f:
    #             f.write(original_text)

    #     for i in range(1, iterations+1):
    #         if i == 1:
    #             cur_files = filepaths
    #         else:
    #             cur_files = []
    #             for val in which_files:
    #                 filename = os.path.basename(filepaths[val])
    #                 filename = filename[:-4] if filename.endswith(".dfy") else filename
    #                 cur_dfy = os.path.join(dir, filename, str(i - 1) + "_refinement.dfy")
    #                 cur_files.append(cur_dfy)
    #         print(cur_files)

    #         feedback = self.spec_feedback(cur_files)
    #         new_feedback = []
    #         new_filepaths = [] 

    #         for j in range(len(feedback)):
    #             lines = feedback[j].splitlines()
    #             if lines[0] == "SPEC NEEDS IMPROVEMENT":
    #                 new_filepaths.append(filepaths[j])
    #                 new_feedback.append("\n".join(lines[1:]))
    #             filename = os.path.basename(filepaths[j])
    #             filename = filename[:-4] if filename.endswith(".dfy") else filename
    #             cur_dir = os.path.join(dir, filename)
    #             os.makedirs(cur_dir, exist_ok=True)
    #             print(dir)
    #             print(cur_dir)
    #             cur_text = os.path.join(cur_dir, str(i) + "_feedback.txt")
    #             with open(cur_text, "w") as f:
    #                 f.write(feedback[j])

    #         refined = self.spec_refinement(new_feedback, new_filepaths)

    #         filepaths = []
    #         for k in range(len(refined)):
    #             filename = os.path.basename(new_filepaths[k])
    #             filename = filename[:-4] if filename.endswith(".dfy") else filename
    #             this_dir = os.path.join(dir, filename)
    #             os.makedirs(this_dir, exist_ok=True)
    #             cur_dfy = os.path.join(this_dir, str(i) + "_refinement.dfy")
    #             filepaths.append(cur_dfy)
    #             with open(cur_dfy, "w") as f:
    #                 f.write(refined[k])
            
    #         print(dir)
    #         print(filepaths)
    
    def feedback_improvement_loop(self, 
                                  iterations: int = 1):
        dir = os.path.join(self.results_dir, "feedback_refinement_loop")
        os.makedirs(dir, exist_ok=True) 

        filepaths = self.get_file_paths()
        dir_list = []

        for filepath in filepaths:
            filename = os.path.basename(filepath)
            filename = filename[:-4] if filename.endswith(".dfy") else filename
            new_dir = os.path.join(dir, filename)
            dir_list.append(new_dir)
            os.makedirs(new_dir, exist_ok=True)
            with open(filepath, "r") as file:
                original_text = file.read()
            with open(os.path.join(new_dir, "0_refinement.dfy"), "w") as f:
                f.write(original_text)

        for i in range(1, iterations+1):
            cur_paths = []
            for i in range(len(dir_list)):
                new_path = os.path.join(str(i-1) + "_refinement.dfy")
                if os.path.exists(new_path):
                    cur_paths.append(new_path)

            print(cur_paths)

            feedback = self.spec_feedback(cur_paths) 
            new_feedback = []
            new_filepaths = [] 

            for j in range(len(feedback)):
                lines = feedback[j].splitlines()
                if lines[0] == "SPEC NEEDS IMPROVEMENT":
                    new_filepaths.append(cur_paths[j])
                    new_feedback.append("\n".join(lines[1:]))
                cur_dir = os.path.dirname(cur_paths[j])
                cur_text = os.path.join(cur_dir, str(i) + "_feedback.txt")
                with open(cur_text, "w") as f:
                    f.write(feedback[j])

            refined = self.spec_refinement(new_feedback, new_filepaths)

            for k in range(len(refined)):
                this_dir = os.path.dirname(new_filepaths[k])
                os.makedirs(this_dir, exist_ok=True)
                cur_dfy = os.path.join(this_dir, str(i) + "_refinement.dfy")
                filepaths.append(cur_dfy)
                with open(cur_dfy, "w") as f:
                    f.write(refined[k])
            
            print(dir)
            print(filepaths)

    def remove_body(self):
        output_dir = os.path.join(self.results_dir, "body_removed")
        input_dir = self.dirs[-1]
        count = 0 
        if not os.path.exists(output_dir):
            os.makedirs(output_dir)
        
        for filename in os.listdir(input_dir):
            count +=1
            file_path = os.path.join(input_dir, filename)
            if os.path.isfile(file_path):
                with open(file_path, 'r') as f:
                    content = f.read()
                    bodyRemoved = remove_body(content, filename)
                    if bodyRemoved is not None:
                        new_file_path = os.path.join(output_dir, filename)
                        with open(new_file_path, 'w') as new_f:
                            new_f.write(bodyRemoved)
        self.dirs.append(output_dir)

        print(f"Total files processed: {count}")
    


