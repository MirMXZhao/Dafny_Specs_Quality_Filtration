method main(x :int) returns (j :int, i :int)
requires x > 0
ensures j == 2 * x
{}


// MODULE main
// 	int i;
// 	int j;
// 	int x;

// 	assume(j == 0);
// 	assume(x > 0);
// 	assume(i == 0);

// 	while(i < x){}

// 	assert(j == 2*x);	

// END MODULE


// (and (not (<= (+ (* 2 i) (* (- 1) j)) (- 1))) (and (not (<= 1 (+ j (* (- 2) x)))) (not (<= 1 (+ (* 2 i) (* (- 1) j))))))


// (and 
// (not (<= (+ (* 2 i) (* (- 1) j)) (- 1)))
// (not (<= 1 (+ j (* (- 2) x)))) 
// (not (<= 1 (+ (* 2 i) (* (- 1) j))))

// (
    // and (not (<= (+ (* 2 i) (* (- 1) j)) (- 1))) (
    //     and (not (<= 1 (+ j (* (- 2) x)))) (not (<= 1 (+ (* 2 i) (* (- 1) j))))))
