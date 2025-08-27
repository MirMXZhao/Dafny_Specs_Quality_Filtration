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
        self.debug_num = 20
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
        filepaths = self.get_file_paths()

        message_prompt = self.prompts["method_name_improvement"]["task"] + self.prompts["method_name_improvement"]["output_request"] + self.prompts["method_name_improvement"]["file"]
        responses = self.concurrency.send_messages_with_progress(
                system_prompt="You are a straightforward assistant to a software engineer who does not talk except to answer the task asked.",
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
            new_filepath = os.path.join(new_dir, filename)

            with open(new_filepath, 'w') as f:
                f.write(response)

        new_text = "====== method_name_improvement completed ======\n\n"
        with open(self.summary_text, "a") as f:
            f.write(new_text)

        self.dirs.append(new_dir)

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
    


