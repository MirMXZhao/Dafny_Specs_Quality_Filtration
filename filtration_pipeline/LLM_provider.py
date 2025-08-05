import os
import openai
from helpers import read_file
import anthropic
from abc import ABC, abstractmethod
from typing import Dict, List, Optional, Union, Any

class LLMProvider(ABC):
    """
    Abstract base class for LLM providers
    """
    
    @abstractmethod
    def __init__(self, api_key: Optional[str] = None):
        """Initialize the provider with API key"""
        pass
    
    @abstractmethod
    def create_message(self, 
                      system_prompt: str, 
                      message_prompt: str, 
                      input_content: Union[str, Dict[str, Any]], 
                      max_tokens: int = 2000, 
                      model: str = "") -> str:
        """Send a message and return the response"""
        pass
    
    @abstractmethod
    def get_default_model(self) -> str:
        """Return the default model for this provider"""
        pass


class AnthropicProvider(LLMProvider): 
    """
    Anthropic LLM API Provider
    """
    
    def __init__(self, api_key: Optional[str] = None):
        if api_key is None:
            api_key = os.getenv("ANTHROPIC_API_KEY")
        if not api_key:
            raise ValueError("ANTHROPIC_API_KEY environment variable not set")
        
        self.client = anthropic.Anthropic(api_key=api_key)
        self._default_model = "claude-sonnet-4-20250514"

    def get_default_model(self) -> str:
        return self._default_model

    def upload_file(self, directory: str, filename: str) -> str:
        """
        Uploads a single file using anthropic file API
        """
        filepath = os.path.join(directory, filename)
        try:
            result = self.client.beta.files.upload(
                file=(filename, open(filepath, "rb"), "text/plain")
            )
            return result
        except Exception as e:
            raise RuntimeError(f"Failed to upload file {filename}: {e}")

    def upload_directory(self, directory: str, extension: str = ".dfy") -> Dict[str, List[str]]:
        """
        Uploads all files in a directory 
        Returns a dictionary mapping filenames to their file IDs
        """
        files = os.listdir(directory) 
        file_ids = {
            "filename": [],
            "id": []
        }

        for file in files:
            if file.endswith(extension):
                try:
                    fileid = self.upload_file(directory, file)
                    file_ids["filename"].append(file)
                    file_ids["id"].append(fileid.id)
                except Exception as e:
                    print(f"Failed to upload {file}: {e}")
                    continue
        
        return file_ids

    def create_message(self, 
                      system_prompt: str, 
                      message_prompt: str, 
                      input_content: Union[str, Dict[str, Any]], 
                      max_tokens: int = 2000, 
                      model: str = "") -> str:
        """
        Sends a message to the model
        """
        if not model:
            model = self._default_model
            
        try:
            # Prepare system content
            system_content = {
                "type": "text",
                "text": system_prompt,
                "cache_control": {"type": "ephemeral"}
            }
            
            # Prepare user content
            user_content = [
                {
                    "type": "text",
                    "text": message_prompt,
                    "cache_control": {"type": "ephemeral"}
                }
            ]
            
            # Add input content
            if isinstance(input_content, str):
                user_content.append({
                    "type": "text",
                    "text": input_content
                })
            else:
                user_content.append(input_content)
            
            response = self.client.beta.messages.create(
                model=model,
                max_tokens=max_tokens,
                system=[system_content],
                messages=[{
                    "role": "user",
                    "content": user_content
                }],
                betas=["files-api-2025-04-14"],
            )
            
            return response.content[0].text
        
        except Exception as e:
            print(f"Error processing message: {str(e)}")
            return "ERROR"

    def create_message_fileid(self, 
                            system_prompt: str, 
                            message_prompt: str, 
                            fileid: str, 
                            max_tokens: int = 2000, 
                            model: str = "") -> str:
        """
        Sends a message based on file ID uploaded using the files API
        """
        input_content = {
            "type": "document",
            "source": {
                "type": "file",
                "file_id": fileid
            }
        }
        return self.create_message(system_prompt, message_prompt, input_content, max_tokens, model)
    
    def create_message_text(self, 
                           system_prompt: str, 
                           message_prompt: str, 
                           file_content: str, 
                           max_tokens: int = 2000, 
                           model: str = "") -> str:
        """
        Sends a message directly based on file content
        """
        return self.create_message(system_prompt, message_prompt, file_content, max_tokens, model)


class OpenAIProvider(LLMProvider): 
    """
    OpenAI LLM API Provider
    """
    
    def __init__(self, api_key: Optional[str] = None):
        if api_key is None:
            api_key = os.getenv("OPENAI_API_KEY")
        if not api_key:
            raise ValueError("OPENAI_API_KEY environment variable not set")
        
        self.client = openai.OpenAI(api_key=api_key)
        self._default_model = "gpt-4"

    def get_default_model(self) -> str:
        return self._default_model

    def create_message(self, 
                      system_prompt: str, 
                      message_prompt: str, 
                      input_content: Union[str, Dict[str, Any]], 
                      max_tokens: int = 2000, 
                      model: str = "") -> str:
        if not model:
            model = self._default_model
            
        try:
            # Prepare the full message content
            if isinstance(input_content, str):
                full_content = f"{message_prompt}\n{input_content}"
            else:
                # For file-based content, just use the message prompt
                full_content = message_prompt
                
            response = self.client.chat.completions.create( 
                model=model,
                messages=[
                    {"role": "system", "content": system_prompt},
                    {"role": "user", "content": full_content}
                ],
                max_tokens=max_tokens
            )
            return response.choices[0].message.content

        except Exception as e:
            print(f"Error processing message: {str(e)}")
            return "ERROR"
    
    def embed_file(self, filepath: str, model: str = "text-embedding-3-small") -> Optional[List[float]]:
        """Generate embedding for a single text"""
        with open(filepath, 'r') as file:
            text = file.read()
        try:
            response = self.client.embeddings.create(
                model=model,
                input=text
            )
            return response.data[0].embedding
        except Exception as e:
            print(f"Error generating embedding: {e}")
            return None
        
    # def embed_files(self, files: List[str]) -> Dict[str, List]:
    #     """
    #     Generate embeddings for multiple files
    #     Returns a dictionary with filenames and their embeddings
    #     """
    #     embedding_results = {
    #         "filename": [],
    #         "embedding": []
    #     }

    #     for filepath in files:
    #         content = read_file(filepath)
    #         if not content: 
    #             continue
            
    #         embedding = self.embed_file(content)
    #         if embedding:
    #             embedding_results["filename"].append(os.path.basename(filepath))
    #             embedding_results["embedding"].append(embedding)
        
    #     return embedding_results


    