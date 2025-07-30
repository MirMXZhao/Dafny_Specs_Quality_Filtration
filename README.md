# Dafny specs Filtration Pipeline

## About
The overall goal of vericoding is to use LLMs to generate fully-verified functions in Dafny based on just the Dafny specification. This repository filters [DafnyBench](https://arxiv.org/abs/2406.08467) for useful specification for use in vericoding, and creates tests to test for program correctness. 

The goal of the original DafnyBench was to test the ability of LLMs to auto-generate hints for the Dafny formal verification engine to successfully complete its verification. To extract the specifications for vericoding, we start by removing the bodies of the functions in DafnyBench. However, because the task of vericoding is different from DafnyBench's original purpose, not all of DafnyBench's specs are appropriate for the task of vericoding. 

This pipeline can be used to filter any future sets of Dafny specifications for quality: it accounts for duplication, difficulty, understandability, etc. Each step is thoroughly checked. 

## Usage 
### Requirements
1. python, os, pandas, threading 
2. Dafny 
3. OpenAPI key, set OPENAI_API_KEY in environment
4. Anthropic key, set ANTHROPIC_API_KEY in environment 

### How it works 
The primary code can be found in DafnyBench/filtration_ai/steps. 
The pipeline is divided into 7 steps, each of which is labelled with s{step number}_{stepdescription}.py
Further details can be found in this [slideshow](https://docs.google.com/presentation/d/1VtDcfhTLdbei7ASAGwJDzfwwEMaWUoMeusueroLxY8I/edit?usp=sharing)

1. Step 1: General filter: filters for simplicity, complexity, and being understandable code
2. Step 2: Manual sanity check: no code. It's recommended to check the results of step 1 at this point and ensure that they are reasonable. 
3. Step 3: Filter for the easier problems
4. Step 4: Sanity check by counting the number of methods that are not specified with requires or ensures statements. 
5. Step 5: Finds duplicates and deletes them
6. Step 6: Generates tests for each function. 
7. Step 7: Fills in implementations for each function. 

The other folders in this repository (DafnyComp, helping_vericoding, and textbook_notes are separate and should be disregarded for now)