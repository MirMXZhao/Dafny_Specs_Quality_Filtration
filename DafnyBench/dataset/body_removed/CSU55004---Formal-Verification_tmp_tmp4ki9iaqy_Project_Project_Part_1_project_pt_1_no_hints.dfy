//This method should return true iff pre is a prefix of str. That is, str starts with pre
method isPrefix(pre:string, str:string) returns(res:bool)
    requires 0 < |pre| <= |str| //This line states that this method requires that pre is less than or equal in length to str. Without this line, an out of bounds error is shown on line 14: "str[i] != pre[i]"
{}

//This method should return true iff sub is a substring of str. That is, str contains sub
method isSubstring(sub:string, str:string) returns(res:bool)
    requires 0 < |sub| <= |str| //This method requires that sub is less than or equal in length to str
{
    //Initialising the index variable
    var i := 0;

    //This variable stores the difference in length between the two strings
    var n := (|str| - |sub|);

    //Here, we want to re-use the "isPrefix" method above, so with each iteration of the search, we are passing an offset of str - effectively trimming a character off the front of str and passing it to isPrefix
        //example 1 (sub found in str): 
        //str = door & sub = or
        //iteration 1: isPrefix(or, door), returns false, trim & iterate again
        //iteration 2: isprefix(or, oor), returns false, trim & iterate again
        //iteration 3: isPrefix(or, or), returns true, stop iterating

        //example 2 (sub not found in str):
        //str = doom & sub = or
        //iteration 1: isPrefix(or, doom), returns false, trim & iterate again
        //iteration 2: isprefix(or, oom), returns false, trim & iterate again
        //iteration 3: isPrefix(or, om), returns false, str is has not been "trimmed" to the same length as sub, so we stop iterating

    while(i < n+1)
    {}
    return false;
}

//This method should return true iff str1 and str1 have a common substring of length k
method haveCommonKSubstring(k:nat, str1:string, str2:string) returns(found:bool)
    requires 0 < k <= |str1| &&  0 < k <= |str2| //This method requires that k > 0 and k is less than or equal to in length to str1 and str2
{
    //Initialising the index variable
    var i := 0;

    //This variable is used to define the end condition of the while loop
    var n := |str1|-k;

    //Here, we want to re-use the "isSubstring" method above, so with each iteration of the search, we are passing a substring of str1 with length k and searching for this substring in str2. If the k-length substring is not found, we "slide" the length-k substring "window" along and search again
        //example:
        //str1 = operation, str2 = rational, k = 5
        //Iteration 1: isSubstring(opera, rational), returns false, slide the substring & iterate again
        //Iteration 2: isSubstring(perat, rational), returns false, slide the substring & iterate again
        //Iteration 3: isSubstring(erati, rational), returns false, slide the substring & iterate again
        //Iteration 4: isSubstring(ratio, rational), returns true, stop iterating

    while(i < n)
    {}
    return false;
}

//This method should return the natural number len which is equal to the length of the longest common substring of str1 and str2. Note that every two strings have a common substring of length zero.
method maxCommonSubstringLength(str1:string, str2:string) returns(len:nat)
    requires 0 < |str1| && 0 < |str1|
{
    //This variable is used to store the result of calling haveCommonKSubstring
    var result:bool;
    
    //We want the longest common substring between str1 and str2, so the starting point is going to be the shorter of the two strings.
    var i:= |str1|;
    if(|str2| < |str1|){}

    //Here, we want to re-use the "haveKCommonSubstring" method above, so with each iteration of the search, we pass a decreasing value of k until a common substring of this length is found. If no common substring is found, we return 0.
    while (i > 0)
    {}
    return 0;
}

//Main to test each method
method Main(){}

