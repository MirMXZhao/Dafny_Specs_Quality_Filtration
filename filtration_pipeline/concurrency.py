import os
import threading
import pandas as pd
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import List, Dict, Any, Optional, Union
from LLM_provider import OpenAIProvider, AnthropicProvider
from helpers import read_file, extract_dafny_code, load_prompts

class Concurrency:
    """
    Handles concurrent processing of LLM requests
    """
    
    def __init__(self, 
                 anthro_provider: AnthropicProvider, 
                 open_provider: OpenAIProvider, 
                 max_workers: int = 10):
        self.anthro_provider = anthro_provider 
        self.open_provider = open_provider
        self.lock = threading.Lock()
        self.max_workers = max_workers

    def send_messages(self, 
                     system_prompt: str, 
                     message_prompt: str, 
                     inputs: List[Any], 
                     provider: str = "anthro", 
                     input_type: str = "text", 
                     max_tokens: int = 2000, 
                     model: str = "",
                     collect_results: bool = True) -> Union[List[Any], List[str]]:
        """
        Send multiple messages concurrently using the selected provider and input type.

        Args:
            system_prompt: The system prompt to send
            message_prompt: The user message prompt
            inputs: List of inputs (file paths, file IDs, or raw text)
            provider: "anthro" or "open"
            input_type: "filepaths", "fileid", or "text"
            max_tokens: Maximum tokens for response
            model: Model to use (uses default if empty)
            collect_results: If True, returns list of responses; if False, returns futures

        Returns:
            List of responses or futures depending on collect_results
        """
        if provider == "anthro":
            handler = self.anthro_provider
            if not model:
                model = handler.get_default_model()
        elif provider == "open":
            handler = self.open_provider
            if not model:
                model = handler.get_default_model()
        else:
            raise ValueError(f"Invalid provider: {provider}. Use 'anthro' or 'open'")

        with ThreadPoolExecutor(max_workers=self.max_workers) as executor:
            futures = []

            for input_item in inputs:
                if provider == "anthro":
                    if input_type == "fileid":
                        future = executor.submit(
                            handler.create_message_fileid, 
                            system_prompt, message_prompt, input_item, max_tokens, model
                        )
                    elif input_type == "filepaths":
                        text = read_file(input_item)
                        future = executor.submit(
                            handler.create_message_text, 
                            system_prompt, message_prompt, text, max_tokens, model
                        )
                    else:  # default text input
                        future = executor.submit(
                            handler.create_message, 
                            system_prompt, message_prompt, input_item, max_tokens, model
                        )
                else:  # OpenAI
                    future = executor.submit(
                        handler.create_message, 
                        system_prompt, message_prompt, input_item, max_tokens, model
                    )
                futures.append(future)

            if collect_results:
                return [future.result() for future in futures]
            else:
                return futures
    
    def send_messages_with_progress(self, 
                                  system_prompt: str, 
                                  message_prompt: str, 
                                  inputs: List[Any], 
                                  provider: str = "anthro", 
                                  input_type: str = "text", 
                                  max_tokens: int = 2000, 
                                  model: str = "",
                                  progress_interval: int = 10) -> List[str]:
        """
        Send messages with progress tracking and better error handling
        """
        if provider == "anthro":
            handler = self.anthro_provider
            if not model:
                model = handler.get_default_model()
        elif provider == "open":
            handler = self.open_provider
            if not model:
                model = handler.get_default_model()
        else:
            raise ValueError(f"Invalid provider: {provider}")

        results = [None] * len(inputs)
        completed = 0
        errors = 0

        with ThreadPoolExecutor(max_workers=self.max_workers) as executor:
            # Submit all tasks
            future_to_index = {}
            for i, input_item in enumerate(inputs):
                if provider == "anthro":
                    if input_type == "fileid":
                        future = executor.submit(
                            handler.create_message_fileid, 
                            system_prompt, message_prompt, input_item, max_tokens, model
                        )
                    elif input_type == "filepaths":
                        text = read_file(input_item)
                        future = executor.submit(
                            handler.create_message_text, 
                            system_prompt, message_prompt, text, max_tokens, model
                        )
                    else:
                        future = executor.submit(
                            handler.create_message, 
                            system_prompt, message_prompt, input_item, max_tokens, model
                        )
                else:
                    future = executor.submit(
                        handler.create_message, 
                        system_prompt, message_prompt, input_item, max_tokens, model
                    )
                future_to_index[future] = i

            # Collect results as they complete
            for future in as_completed(future_to_index):
                idx = future_to_index[future]
                try:
                    result = future.result()
                    results[idx] = result
                    completed += 1
                except Exception as e:
                    print(f"Error processing input {idx}: {e}")
                    results[idx] = f"ERROR: {str(e)}"
                    errors += 1
                
                # Print progress
                if completed % progress_interval == 0 or completed == len(inputs):
                    print(f"Progress: {completed}/{len(inputs)} completed, {errors} errors")

        print(f"Completed: {completed}/{len(inputs)}, Errors: {errors}")
        return results
    
    def embed_texts(self, 
                   texts: List[str], 
                   model: str = "text-embedding-3-small") -> List[Optional[List[float]]]:
        """
        Concurrently embed a list of texts using the OpenAIProvider.
        Returns a list of embeddings (same order as input).
        """
        embeddings = [None] * len(texts)

        with ThreadPoolExecutor(max_workers=self.max_workers) as executor:
            future_to_index = {
                executor.submit(self.open_provider.embed_file, text, model): i
                for i, text in enumerate(texts)
            }

            for future in as_completed(future_to_index):
                idx = future_to_index[future]
                try:
                    embedding = future.result()
                    with self.lock:
                        embeddings[idx] = embedding
                except Exception as e:
                    print(f"[Concurrency] Error embedding text at index {idx}: {e}")
                    embeddings[idx] = None

        return embeddings
    
    def process_with_retries(self, 
                           func, 
                           inputs: List[Any], 
                           max_retries: int = 3, 
                           retry_delay: float = 1.0) -> List[Any]:
        """
        Process inputs with automatic retries for failed operations
        """
        def process_with_retry(input_item):
            for attempt in range(max_retries):
                try:
                    return func(input_item)
                except Exception as e:
                    if attempt == max_retries - 1:
                        print(f"Failed after {max_retries} attempts: {e}")
                        return f"ERROR: {str(e)}"
                    else:
                        import time
                        time.sleep(retry_delay * (2 ** attempt))  # Exponential backoff
            return "ERROR: Max retries exceeded"

        with ThreadPoolExecutor(max_workers=self.max_workers) as executor:
            futures = [executor.submit(process_with_retry, item) for item in inputs]
            return [future.result() for future in futures]
    

