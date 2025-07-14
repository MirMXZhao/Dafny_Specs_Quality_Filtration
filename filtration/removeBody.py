import os

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
    

#removes bodies of functions
def removeBody(text, filename):
    bracePairs = allBracePairs(text, filename)
    if bracePairs is None:
        return None
    
    result = list(text)
    print(bracePairs)
    for start, end in reversed(bracePairs):
        # this ensures that we dont remove nested functions/lemmas/methods (ie methods that are part of a class)
        if "method" in text[start + 1: end] or "lemma" in text[start + 1: end] or "function" in text[start + 1: end] or "class" in text[start + 1: end]:
            newInner = removeBody(text[start + 1: end], filename)
            if newInner is not None:
                newInner = list(newInner)
                del result[start+1:end]
                result[start+1: start+1] = newInner 
        else:
            if end - start > 20: # this should help ensure we do not remove the interior of sets 
                del result[start+1:end] # deletes everything in the middle (but not the braces themselves)
    return ''.join(result)

if __name__ == "__main__":
    directory = "DafnyBench/DafnyBench/dataset/hints_removed"
    total_files = 0 
    new_files = 0
    for filename in os.listdir(directory):
        file_path = os.path.join(directory, filename)
        if os.path.isfile(file_path):
            total_files +=1 
            with open(file_path, 'r') as f:
                content = f.read()
                bodyRemoved = removeBody(content, filename)
                if bodyRemoved is not None:
                    new_files += 1
                    new_file_path = os.path.join("DafnyBench/DafnyBench/dataset/body_removed/", filename)
                    with open(new_file_path, "w") as f:
                        f.write(bodyRemoved)

    print(f"Total files: {total_files}")
    print(f"New files: {new_files}")