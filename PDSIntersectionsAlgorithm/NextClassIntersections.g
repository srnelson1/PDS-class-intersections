
##############################################################################################################
####LIST GENERATION###########################################################################################

#This section is dedicated to generating all lsts. The code is built to generate a lst in linear order
#in the sense that beginning with a starting lst, cl_ints, we repeatedly apply NextClassIntersection
#to cl_ints, and generate all possible lsts without backtracking.

#We achieve this behavior subject to two constraints, each lst must sum to an identical quantity called stack_size,
#and the ith posn in each lst is strictly bounded by some value specified in ceiling[i] (the interpretation for
#these values is given in AllClassIntersections). So, we initialize by entering a stacks_lst [a_1, ..., a_r] such that 
#j is the smallest value for which a_j, ..., a_r = 0, respecting the constraint Sum(stacks_lst) = stack_size and
#a_i <= ceiling[i]. Psuedo code is given for the main process above NextClassIntersection.

RightmostNonzeroPosition := function(cl_ints, partn_ceiling)
	local i, lst_size;

	lst_size := Size(cl_ints);

	for i in [0..(lst_size-1)] do
		if cl_ints[lst_size - i] <> 0 and cl_ints[lst_size-i] <= partn_ceiling[lst_size-i] then
			return lst_size - i;
			break;
		fi;
	od;

	return "All Zeroes";
end;

#If pickup_stack = max_stack, returns done. Otherwise, iterates through rightmost_pos..Size(stacks_lst) and places as much of
#pickup_stack at rightmost_pos while respecting ceiling. if Sum(ceiling{[rightmost_pos..Size(stacks_lst)]}) < pickup_stack and
#pickup_stack <> max_stack, then the above operation is impossible and we return Unplaceable.
PlaceStack := function(cl_ints, partn_ceiling, rightmost_pos, pickup_stack, max_stack)
	local i, min_stack_ceil;

	if Sum(partn_ceiling{[rightmost_pos..Size(cl_ints)]}) < pickup_stack then
		if pickup_stack = max_stack then
			return "Done";
		fi;

		return "Unplaceable";
	fi;

	for i in [rightmost_pos..Size(cl_ints)] do
		min_stack_ceil := Minimum([pickup_stack, partn_ceiling[i]]);
		cl_ints[i] := cl_ints[i] + min_stack_ceil;
		
		if min_stack_ceil = pickup_stack then
			break;
		fi;

		pickup_stack := pickup_stack-min_stack_ceil;
	od;

	return cl_ints;
end;

#Takes in a lst [a_1, ..., a_n, 0, 0, ..., 0]. Initializes pickup_stack := 0. Then
#   1) Search for rightmost nonzero posn, rightmost_pos.
#   2) Subtract 1 from rightmost_pos and add 1 to pickup_stack.
#   3) Search for next possible posn in [rightmost_pos+1..end_of_lst] to place pickup_stack which respects ceiling.
#   4) If no next posn exists, check if pickup_stack contains all values of input lst.
#   5) If yes, then quite, otherwise return to step 1.
NextClassIntersection := function(cl_ints, partn_ceiling, stack_size, cl_ints_len)
	local max_stack, lst_size, check_placeable, rightmost_pos, pickup_stack, next_posn;

	max_stack := stack_size;

	if RightmostNonzeroPosition(cl_ints{[1..cl_ints_len]}, partn_ceiling) = "All Zeroes" then
		return "Done";
	fi;

	pickup_stack := 0;
	check_placeable := "Unplaceable";

	while check_placeable = "Unplaceable" do
		rightmost_pos := RightmostNonzeroPosition(cl_ints, partn_ceiling);

		if rightmost_pos = cl_ints_len + 1 then 
			pickup_stack := pickup_stack + cl_ints[rightmost_pos];
			cl_ints[rightmost_pos] := 0;
			rightmost_pos := RightmostNonzeroPosition(cl_ints, partn_ceiling);
		fi;

		cl_ints[rightmost_pos] := cl_ints[rightmost_pos] - 1;
		pickup_stack := pickup_stack + 1;
		
		check_placeable := PlaceStack(cl_ints, partn_ceiling, rightmost_pos + 1, pickup_stack, max_stack);
	od;

	if check_placeable = "Done" then
		return "Done";
	fi;

	return cl_ints;
end;

