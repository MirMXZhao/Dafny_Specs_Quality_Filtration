
import argparse
import sys
import time
from pathlib import Path
from steps import Pipeline
from concurrency import Concurrency
from LLM_provider import AnthropicProvider, OpenAIProvider

def test():
    pipeline = Pipeline(max_workers = 10)
    # pipeline.step_one_filter_layer_1(debug = True)
    # pipeline.step_two_filter_layer_2(debug = True)
    pipeline.step_three_sanity_check(debug = True)


if __name__ == "__main__":
    test() 