
import argparse
import sys
import time
from pathlib import Path
from Pipeline import Pipeline
from Concurrency import Concurrency
from LLM_provider import AnthropicProvider, OpenAIProvider

def test():
    pipeline = Pipeline(run_num=0, max_workers = 10)
    pipeline.run_subset([1,2,3,4,5,6], debug=True)

def mirandaTest():
    pipeline = Pipeline(run_num=0, max_workers = 10, starting_xlsx="7_s4_duplicates.xlsx")
    pipeline.run_subset([3])
    # pipeline.step_one_filter_layer_1(debug=True)
    # pipeline.step_two_filter_layer_2()
    # pipeline.step_three_sanity_check(debug=True)
    # pipeline.step_four_delete_duplicates()
    # pipeline.step_five_unify_format()
    # pipeline.step_six_create_tests(debug=True)

def user_usage(): 
    pipeline = Pipeline(run_num = 3
                        ,max_workers = 15
                        ,root_dir = "** YOUR DIRECTORY HERE **")
    pipeline.run_subset([1, 2, 3, 4, 5, 6], debug=True)

if __name__ == "__main__":
    test()
    # user_usage()