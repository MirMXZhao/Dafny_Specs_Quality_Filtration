
import argparse
import sys
import time
from pathlib import Path
from filtration_pipeline import FiltrationPipeline, FilterType
from Concurrency import Concurrency
from LLM_provider import AnthropicProvider, OpenAIProvider
from refinement_pipeline import RefinementPipeline

def test():
    pipeline = FiltrationPipeline(run_num=5, root_dir = "./DafnyBench/DafnyBench/dataset/new_body_removed", max_workers = 10)
    pipeline.run_full_pipeline()

def mirandaTest():
    pipeline = FiltrationPipeline(run_num=5, max_workers = 10, mode = "evaluate_pipeline")
    # pipeline.step_one_filter(FilterType.one)
    # pipeline.step_one_filter(FilterType.two)
    # # pipeline.step_one_run_full()
    # pipeline.step_two_sanity_check()
    # pipeline.step_three_unify_format()
    # pipeline.delete_duplicates()
    # pipeline.create_tests()
    pipeline.summarize_filtration()
    # pipeline.step_two_filter_layer_2_pt2()
    # pipeline.compare_results(input_file = "2_understandable_filter_s2_filter.xlsx")
    # pipeline.compare_results(input_file = "3_fully_specified_filter_s2_filter.xlsx")

    # pipeline.run_subset([3])
    # pipeline.step_one_filter_layer_1(debug=True)
    # pipeline.step_two_filter_layer_2()
    # pipeline.step_three_sanity_check(debug=True)
    # pipeline.step_four_delete_duplicates()
    # pipeline.step_five_unify_format()
    # pipeline.step_six_create_tests(debug=True)

def refinementTest():
    pipeline = RefinementPipeline(0, debug = True)
    pipeline.method_name_improvement()


def user_usage(): 
    pipeline = FiltrationPipeline(run_num = 3
                        ,max_workers = 15
                        ,root_dir = "** YOUR DIRECTORY HERE **")
    pipeline.run_subset([1, 2, 3, 4, 5, 6], debug=True)

if __name__ == "__main__":
    # refinementTest()
    mirandaTest()
    # test()
    # user_usage()