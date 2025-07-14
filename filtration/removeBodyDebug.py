import os
import os
import re
import heapq

# in a string text, returns list of all pairs of corresponding braces that are not contained in other braces. 
def allBracePairs(text, filename):
    stack = []
    pairs = []

    for i, c in enumerate(text):
        if c == '{':
            stack.append(i)
        elif c == '}':
            if not stack:
                print("Unmatched closing brace at index", i)
                print(filename)
                return None
            start = stack.pop()
            # Only add pair if it's top-level (i.e., when stack is empty *after* popping)
            if not stack:
                pairs.append((start, i))
    return pairs
    
def find_noncommented_statement_indices(text, words):
    indices = []
    current_index = 0
    for word in words:
        phrase = r'\b' + re.escape(word) + r'\b'

        in_block_comment = False

        for line in text.splitlines(keepends=True):  # preserve line breaks
            code = ''
            i = 0
            while i < len(line):
                if in_block_comment:
                    end = line.find('*/', i)
                    if end == -1:
                        # Still inside block comment
                        i = len(line)
                    else:
                        in_block_comment = False
                        i = end + 2
                elif line.startswith('//', i):
                    # Line comment starts, skip the rest of the line
                    break
                elif line.startswith('/*', i):
                    in_block_comment = True
                    i += 2
                else:
                    code += line[i]
                    i += 1

            # Find matches in code portion only
            for match in re.finditer(phrase, code):
                indices.append(current_index + match.start())

            current_index += len(line)

        if len(indices) > 0:
            print("found word " + word)
            return True
        
    return False

#removes bodies of functions
def removeBody(text, filename):
    bracePairs = allBracePairs(text, filename)
    if bracePairs is None:
        return None
    
    result = list(text)
    print(bracePairs)

    keywords = {"method", "lemma", "predicate", "class"}
    for start, end in reversed(bracePairs):
        # this ensures that we dont remove nested functions/lemmas/methods (ie methods that are part of a class)
        if find_noncommented_statement_indices(text[start + 1:end], keywords):
            print("new inner!")
            print("cur Inner " + text[start + 1:end])
            newInner = removeBody(text[start + 1: end], filename)
            print("new Inner " + newInner)
            if newInner is not None:
                newInner = list(newInner)
                del result[start+1:end]
                result[start+1: start+1] = newInner 
        else:
            if end - start > 20: # this should help ensure we do not remove the interior of sets 
                del result[start+1:end] # deletes everything in the middle (but not the braces themselves)
    return ''.join(result)

if __name__ == "__main__":
    file_path = "/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/filtration/example_code_2.dfy"
    filename = "example_code_2.dfy"
    total_files = 0 
    new_files = 0
    print("hello!")

    with open(file_path, 'r') as f:
        content = f.read()
        print("content" + content)
        bodyRemoved = removeBody(content, filename)
        print(bodyRemoved)
        if bodyRemoved is not None:
            new_files += 1
