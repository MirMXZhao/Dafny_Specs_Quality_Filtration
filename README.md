# Dafny specs Filtration Pipeline

## About
The overall goal of vericoding is to use LLMs to generate fully-verified functions in Dafny based on just the Dafny specification. This pipeline can be used to filter any future sets of Dafny specifications for quality: it accounts for duplication, difficulty, understandability, etc. Each step is thoroughly checked. 

For the purposes of this project, we filter [DafnyBench](https://arxiv.org/abs/2406.08467) for useful specification for use in vericoding, and creates tests to test for program correctness. There is a currently also an experimental pipeline to refine the original specifications that is being developed. 

The goal of the original DafnyBench was to test the ability of LLMs to auto-generate hints for the Dafny formal verification engine to successfully complete its verification. To extract the specifications for vericoding, we start by removing the bodies of the functions in DafnyBench. However, because the task of vericoding is different from DafnyBench's original purpose, not all of DafnyBench's specs are appropriate for the task of vericoding. 

## Methodology
The pipeline is divided into 5 sections:

1. Filters  
    a. easyness filters (filters out files of easier problems, where easy is defined as problems where the specs are direct formulas for the implementations)
    b. understandability filter (filters out problems that aren't understandable, where understandable is defined as problems that are reasonably interpretable from their name or specification)
    c. fully specified filter (optional, filters out problems that aren't fully specified)
2. Method + ensures/requires statement count check (filters out files where many functions are missing ensures/require statements)
3. Format Unification (deletes unnecessary comments from files)
4. Duplicate Deletion (see paper for more info)
5. Test Creation (creates test methods) 

The pipeline has two modes. 
The default mode runs the pipeline all files. 
The evaluate_pipeline mode runs the pipeline on a subset of 50 files that have been manually examined by a human (me!). It then runs on the pipeline on only these files, and compares the human results to the pipeline results. This mode was used to inform and refine the pipeline.

## Structure
```
├── DafnyBench/DafnyBench/dataset/body_removed      #specs part of the original DafnyBench, with the body removed
│   ├── 630-dafny_tmp_tmpz2kokaiq_Solution_no_hints.dfy
│   ├── 703FinalProject_tmp_tmpr_10rn4z_DP-GD_no_hints.dfy
│   ...
├── filtration_pipeline/
│   ├── automated_count.py                          # Counts the number of functions with no ensures statements
│   ├── Concurrency.py                              # Operates running LLMS with threads
│   ├── DuplicateFinder.py                          # Finds similar files for step 4
│   ├── helpers.py                                  # Few helper functions to read prompts and files
│   ├── LLM_provider.py                             # OpenAI and Anthropic classes
│   ├── main.py                                     # Starting point of running the pipeline
│   ├── Pipeline.py                                 # Steps of the pipeline
│   ├── prompts.yaml                                # Prompts fed to the LLMs
│   ├── prompts.yaml                                # Prompts fed to the LLMs
│   ├── prompts.yaml                                # Prompts fed to the LLMs
├── run_{run_num}/
│   ├──  manual_check                               # 15 files kept and tossed and LLM reasoning, for user checking
│   │   ├── 1_easyness_filter_manual_check.dfy
│   │   ├── 2_understandable_filter_manual_check.dfy
│   │   ...
│   ├──  new_filtered                               # Results of step 5: specs with unnecessary comments and methods (empty test() and Main() methods) removed 
│   │   ├── 0_dafny-synthesis_task_id_598_no_hints.dfy
│   │   ├── 1_dafny-synthesis_task_id_567_no_hints.dfy
│   │   ...
│   ├──  new_tests                                  # Results of step 6: tests for each method of each file
│   │   ├── 0_dafny-synthesis_task_id_598_no_hints.dfy
│   │   ├── 1_dafny-synthesis_task_id_567_no_hints.dfy
│   │   ...
│   ├──  results                                    # Summary of final decisions to keep/toss each file and the LLM outputs
│   │   ├── 0_initial_spreadsheet.xlsx
│   │   ├── 1_easyness_filter.xlsx
│   │   ├── 2_understandable_filter.xlsx 
│   │   ...
│   ├── summary.txt                                 # Summarizes the results of each step
│   ├── results_summary.xlsx                        # Summarizes where each file was discarded and the reasoning
└── ...
```
## Filtration Pipeline
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
1. You can run any group of steps in any order
2. You can set a different bound for step 4 by running step_four_delete_duplicates(bound = 0.7). The default is 
3. You can reuse your results across multiple runs by setting starting_xlsx=("4_s5_unify.xlsx", 4) and run_num = {previous run number} which would start you from file "4_s5_unify.xlsx" from your previous run. 
4. You can choose to debug at any step, which will only run that step on 10 random files. 


### Outputs
A full example of the outputs can be found in run_1 (except for step 2)

The code has several different outputs:
1. Progress, directly into the terminal. Every 10 completed LLM calls are indicated on the screen
2. A run_{run_num} folder, with:
    - A spreadsheet of results under the results folder. Each step outputs an excel sheet with the indication of whether it was decided to keep that file at the step. It also has the explanations of the decisions to keep/toss each file where applicable. 
    - A file with a randomly drawn subset of 15 kept files and 15 tossed files under the manual_check folder. It also contains the explanation for why each file was kept/tossed. This is to allow the user to examine the output at each step of the pipeline and ensure that it is running correctly
    - Newly created files under new_filtered and new_tests for step 5 and 6 respectively, where step 5 deletes the Main function and unnecessary comments, and step 6 adds tests. 
    - A summary of the steps run, the inputs and outputs, and how many files were kept/tossed under summary.txt 
    - A summary of which step each file was eliminated at and why under results_summary.xlsx 

*Naming Convention*: the results of a step are saved in {step_run_num}_{step_name}.xlsx. step_run_num indicates that the input for this step was step_run_num-1. For example, running 4_unify follows 3_easyness_filter.

## Refinement Pipeline
This is currently under development. 
Some of the features currently planned/in place include: 
1. Method name refinement (having the LLM rename only the methods based on context clues to be more descriptive)
2. 


