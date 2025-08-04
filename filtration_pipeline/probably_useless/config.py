# import os
# from typing import Optional, Dict, Any
# from dataclasses import dataclass

# @dataclass
# class PipelineConfig:
#     """Configuration for the filtration pipeline"""
    
#     # Concurrency settings
#     max_workers: int = 10
    
#     # Model settings
#     anthropic_model: str = "claude-sonnet-4-20250514"
#     openai_model: str = "gpt-4"
    
#     # API settings
#     anthropic_api_key: Optional[str] = None
#     openai_api_key: Optional[str] = None
    
#     # Processing settings
#     max_tokens: int = 2000
#     max_retries: int = 3
#     retry_delay: float = 1.0
    
#     # File paths
#     prompts_path: str = "prompts.yaml"
#     output_dir: str = "./results"
    
#     # Progress settings
#     progress_interval: int = 10
    
#     def __post_init__(self):
#         """Validate and set default API keys"""
#         if self.anthropic_api_key is None:
#             self.anthropic_api_key = os.getenv("ANTHROPIC_API_KEY")
#         if self.openai_api_key is None:
#             self.openai_api_key = os.getenv("OPENAI_API_KEY")
    
#     @classmethod
#     def from_dict(cls, config_dict: Dict[str, Any]) -> 'PipelineConfig':
#         """Create config from dictionary"""
#         return cls(**config_dict)
    
#     def to_dict(self) -> Dict[str, Any]:
#         """Convert config to dictionary"""
#         return {
#             'max_workers': self.max_workers,
#             'anthropic_model': self.anthropic_model,
#             'openai_model': self.openai_model,
#             'max_tokens': self.max_tokens,
#             'max_retries': self.max_retries,
#             'retry_delay': self.retry_delay,
#             'prompts_path': self.prompts_path,
#             'output_dir': self.output_dir,
#             'progress_interval': self.progress_interval
#         }
    
#     def validate(self) -> bool:
#         """Validate configuration"""
#         if not self.anthropic_api_key:
#             raise ValueError("ANTHROPIC_API_KEY not set")
#         if not self.openai_api_key:
#             raise ValueError("OPENAI_API_KEY not set")
#         if self.max_workers <= 0:
#             raise ValueError("max_workers must be positive")
#         if self.max_tokens <= 0:
#             raise ValueError("max_tokens must be positive")
#         return True 