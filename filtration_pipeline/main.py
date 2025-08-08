
import argparse
import sys
import time
from pathlib import Path
from Pipeline import Pipeline
from Concurrency import Concurrency
from LLM_provider import AnthropicProvider, OpenAIProvider

def test():
    pipeline = Pipeline(run_num=0, max_workers = 10)
    # pipeline.step_one_filter_layer_1()
    # pipeline.step_two_filter_layer_2()
    # pipeline.step_three_sanity_check()
    # pipeline.step_four_delete_duplicates()
    # pipeline.step_five_unify_format(debug=True)
    # pipeline.step_six_create_tests(debug=True)

if __name__ == "__main__":
    test() 