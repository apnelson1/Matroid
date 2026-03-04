- For every crossing, we can perturb it and get one point inside and one point outside that are suitably close to the crossing.
- Consider the sub-path that starts at the inside point and ends at the outside point and does not intersect the crossing we started with
- This must have some crossing
- Define a function from crossings to crossings by outputing the first crossing in the sub-path
- This function is involutive (for some reason)
- This function is fixed point free by simplicity. If i is mapped to the crossing and we come back to the crossing, 
	1. if we are at i again, then we have traversed the entire polygonal path. At any point, we couldn't have been in outsider without a crossing. We never traversed the outside point, contradiction.
	2. If we are not at i, we have two distinct values being mapped to the same crossing. The path is not simple, contradiction.
- Finite, and existence of involutive, fixed-point-free function proves even.
