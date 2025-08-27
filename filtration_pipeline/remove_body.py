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
            return True
        
    return False

def is_predicate_definition(text, brace_start):
    """
    Check if the brace at brace_start is part of a predicate definition.
    Looks for 'predicate' keyword before the opening brace.
    """
    # Get the text before the opening brace
    before_brace = text[:brace_start]
    
    # Split into lines and look at the last few lines
    lines = before_brace.split('\n')
    
    # Check the last few lines for predicate definition
    for i in range(max(0, len(lines) - 3), len(lines)):
        line = lines[i].strip()
        # Look for predicate keyword followed by identifier
        if re.search(r'\bpredicate\s+\w+', line):
            return True
    
    return False

#removes bodies of some methods
def remove_body(text, filename):
    bracePairs = allBracePairs(text, filename)
    if bracePairs is None:
        return None
    
    result = list(text)

    keywords = {"method", "lemma", "class"}
    for start, end in reversed(bracePairs):
        # this ensures that we dont remove nested functions/lemmas/methods (ie methods that are part of a class)
        if find_noncommented_statement_indices(text[start + 1:end], keywords):
            newInner = remove_body(text[start + 1: end], filename)
            if newInner is not None:
                newInner = list(newInner)
                del result[start+1:end]
                result[start+1: start+1] = newInner 
        else:
            # Check if this brace pair is part of a predicate definition
            if is_predicate_definition(text, start):
                # Skip predicates - don't remove their bodies
                continue
            if end - start > 20: # this should help ensure we do not remove the interior of sets 
                del result[start+1:end] # deletes everything in the middle (but not the braces themselves)
    return ''.join(result)

if __name__ == "__main__":
    directory = "/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/hints_removed"
    # total_files = 0 
    # new_files = 0
    # for filename in os.listdir(directory):
    #     file_path = os.path.join(directory, filename)
    #     if os.path.isfile(file_path):
    #         total_files +=1 
    #         with open(file_path, 'r') as f:
    #             content = f.read()
    #             bodyRemoved = removeBody(content, filename)
    #             if bodyRemoved is not None:
    #                 new_files += 1
    #                 new_file_path = os.path.join("/Users/cinnabon/Documents/MIT/UROP_2025/DafnyBench/DafnyBench/dataset/body_removed", filename)
    #                 with open(new_file_path, "w") as f:
    #                     f.write(bodyRemoved)

    # print(f"Total files: {total_files}")
    # print(f"New files: {new_files}")