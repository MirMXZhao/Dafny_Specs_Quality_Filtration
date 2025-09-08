
import argparse
import sys
import time
from pathlib import Path
from filtration_pipeline import FiltrationPipeline, FilterType
from Concurrency import Concurrency
from LLM_provider import AnthropicProvider, OpenAIProvider
from refinement_pipeline import RefinementPipeline

def testDafnyBench():
    pipeline = FiltrationPipeline(run_num=5, root_dir = "./DafnyBench/DafnyBench/dataset/new_body_removed", max_workers = 10)
    pipeline.run_full_pipeline()

def user_usage(): 
    pipeline = FiltrationPipeline(run_num = 3
                        ,max_workers = 15
                        ,root_dir = "** YOUR DIRECTORY HERE **")
    pipeline.run_subset([1, 2, 3, 4, 5, 6], debug=True)

def filtrationTest():
    pipeline = FiltrationPipeline(run_num=7, root_dir = "/Users/cinnabon/Documents/MIT/UROP_2025/refine_run_0/method_name_improved", max_workers = 10, mode = "evaluate_pipeline")
    pipeline.filter(FilterType.one, debug = True)
    pipeline.filter(FilterType.two)
    pipeline.sanity_check()
    # pipeline.unify_format()
    # pipeline.delete_duplicates()
    # pipeline.create_tests()

def refinementTest():
    pipeline = RefinementPipeline(2, debug = True, dir = "/Users/cinnabon/Documents/MIT/UROP_2025/refine_run_0/method_name_improved")
    pipeline.feedback_improvement_loop(iterations = 2)

if __name__ == "__main__":
    # refinementTest()
    filtrationTest()
    # test()
    # user_usage()