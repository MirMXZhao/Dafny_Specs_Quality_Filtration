# #!/usr/bin/env python3
# """
# Main runner for the filtration pipeline
# """

# import argparse
# import sys
# import os
# from pathlib import Path

# from steps import Pipeline
# from config import PipelineConfig
# from LLM_provider import AnthropicProvider, OpenAIProvider


# def main():
#     """Main entry point"""
#     parser = argparse.ArgumentParser(
#         description="Run the Dafny filtration pipeline"
#     )
#     parser.add_argument(
#         "--config",
#         type=str,
#         help="Path to configuration file (JSON/YAML)"
#     )
#     parser.add_argument(
#         "--max-workers",
#         type=int,
#         default=10,
#         help="Number of concurrent workers"
#     )
#     parser.add_argument(
#         "--anthropic-model",
#         type=str,
#         default="claude-sonnet-4-20250514",
#         help="Anthropic model to use"
#     )
#     parser.add_argument(
#         "--openai-model",
#         type=str,
#         default="gpt-4",
#         help="OpenAI model to use"
#     )
#     parser.add_argument(
#         "--max-tokens",
#         type=int,
#         default=2000,
#         help="Maximum tokens for LLM responses"
#     )
#     parser.add_argument(
#         "--output-dir",
#         type=str,
#         default="./results",
#         help="Output directory for results"
#     )
#     parser.add_argument(
#         "--step",
#         type=int,
#         choices=[1, 2, 3, 4],
#         help="Run only a specific step"
#     )
#     parser.add_argument(
#         "--test-providers",
#         action="store_true",
#         help="Test LLM providers before running pipeline"
#     )
    
#     args = parser.parse_args()
    
#     # Create configuration
#     config = PipelineConfig(
#         max_workers=args.max_workers,
#         anthropic_model=args.anthropic_model,
#         openai_model=args.openai_model,
#         max_tokens=args.max_tokens,
#         output_dir=args.output_dir
#     )
    
#     try:
#         config.validate()
#     except ValueError as e:
#         print(f"Configuration error: {e}")
#         sys.exit(1)
    
#     # Test providers if requested
#     if args.test_providers:
#         print("Testing LLM providers...")
#         try:
#             anthro_provider = AnthropicProvider(config.anthropic_api_key)
#             openai_provider = OpenAIProvider(config.openai_api_key)
#             print("✓ Both providers initialized successfully")
#         except Exception as e:
#             print(f"✗ Provider initialization failed: {e}")
#             sys.exit(1)
    
#     # Create pipeline
#     pipeline = Pipeline(
#         max_workers=config.max_workers,
#         anthro_model=config.anthropic_model,
#         open_model=config.openai_model,
#         prompts_path=config.prompts_path
#     )
    
#     # Run specific step or full pipeline
#     if args.step:
#         print(f"Running step {args.step}...")
#         if args.step == 1:
#             results = pipeline.step_one_filter_problems(
#                 output_file=os.path.join(config.output_dir, "step1_filter_problems.xlsx")
#             )
#         elif args.step == 2:
#             results = pipeline.step_two_sanity_check(
#                 output_file=os.path.join(config.output_dir, "step2_sanity_check.xlsx")
#             )
#         elif args.step == 3:
#             results = pipeline.step_three_filter_layer_2(
#                 output_file=os.path.join(config.output_dir, "step3_filter_layer2.xlsx")
#             )
#         elif args.step == 4:
#             results = pipeline.step_four_sanity_check_2(
#                 output_file=os.path.join(config.output_dir, "step4_sanity_check2.xlsx")
#             )
#         print(f"Step {args.step} completed")
#     else:
#         print("Running full pipeline...")
#         results = pipeline.run_full_pipeline(
#             output_dir=config.output_dir
#         )
#         print("Full pipeline completed")
    
#     print(f"Results saved to {config.output_dir}")


# if __name__ == "__main__":
#     main() 