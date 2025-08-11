# Dafny specs Filtration Pipeline

## About
The overall goal of vericoding is to use LLMs to generate fully-verified functions in Dafny based on just the Dafny specification. This pipeline can be used to filter any future sets of Dafny specifications for quality: it accounts for duplication, difficulty, understandability, etc. Each step is thoroughly checked. 

For the purposes of this project, we filter [DafnyBench](https://arxiv.org/abs/2406.08467) for useful specification for use in vericoding, and creates tests to test for program correctness. 

The goal of the original DafnyBench was to test the ability of LLMs to auto-generate hints for the Dafny formal verification engine to successfully complete its verification. To extract the specifications for vericoding, we start by removing the bodies of the functions in DafnyBench. However, because the task of vericoding is different from DafnyBench's original purpose, not all of DafnyBench's specs are appropriate for the task of vericoding. 

## Methodology
The pipeline is divided into 7 steps, each of which is labelled with s{step number}_{stepdescription}.py

0. Step 0: Creates a spreadsheet of all files in the repository 
1. Step 1: General filter: filters for simplicity, complexity, and understandability
    Outputs:
2. Step 2: Filter out the easier problems
3. Step 3: Sanity check by counting the number of methods that are not specified with requires or ensures statements. 
4. Step 4: Finds duplicates and deletes them
5. Step 5: Deletes unnecessary comments and code
6. Step 6: Generates tests for each function.

## Usage
A pipeline is provided for easy, robust use on any folder of Dafny specifications. 
All code for the pipeline can be found in the filtration_pipeline folder

### Requirements
1. python, os, pandas, threading 
2. Dafny 
3. OpenAPI key, set OPENAI_API_KEY in environment
4. Anthropic key, set ANTHROPIC_API_KEY in environment 

### Testing on DafnyBench

To first test the pipeline on DafnyBench (with the provided files in the repo), navigate to filtration_pipeline/main.py and ensure that test() is running.

Running the main.py file will run the debugging version of the full pipeline, which means that all steps of the pipeline will be run on a subset of 30 files. 

### Running on a Custom Dataset

To run on a custom dataset, create a folder with all Dafny specifications you want to check. Go to the user_usage() method of the main.py file and replace "** YOUR DIRECTORY HERE **" with your directory. 

The current code will run the full pipeline on a subset of 30 files in your specifications. To run the pipeline on all your files, set debug to False. 

### Customization

There are several options for customization. 
1. You can run any group of steps in any order, and duplicates are allowed. For example, if you want to run steps 5, 3, 4, 2, 2, 1 in that order, you can do so by running pipeline.run_subset([5, 3, 4, 2, 2, 1])
2. You can run steps 1 and 2 n times, and decide to keep a file if the at least m of the LLM results decided to keep that file. This can be done by running repeated_step_run(step = 1, 3, 2). This would run the LLM on step one 3 times, and only decided to keep a file if it decided to keep the file at least 2 times. This can help you account for inaccuracies in the LLM. 
3. You can set a different bound for step 4 by running step_four_delete_duplicates(bound = 0.7)
4. You can reuse your results across multiple runs by setting starting_xlsx=("4_s5_unify.xlsx", 4) which would start you from file "4_s5_unify.xlsx" from your previous run. 



### Outputs

The code has several different outputs:
1. Progress, directly into the terminal. Every 10 completed LLM calls are indicated on the screen
2. A run_{run_num} folder, with:
    - A spreadsheet of results under the results folder. Each step outputs an excel sheet with the indication of whether it was decided to keep that file at the step. It also has the explanations of the decisions to keep/toss each file where applicable. 
    - A file with a randomly drawn subset of 15 kept files and 15 tossed files under the manual_check folder. It also contains the explanation for why each file was kept/tossed. This is to allow the user to examine the output at each step of the pipeline and ensure that it is running correctly
    - Newly created files under new_filtered and new_tests for step 5 and 6 respectively, where step 5 deletes the Main function and unnecessary comments, and step 6 adds tests. 
    - A summary of the steps run, the inputs and outputs, and how many files were kept/tossed under summary.txt 


