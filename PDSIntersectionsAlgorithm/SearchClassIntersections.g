Read("NextClassIntersections.g");
Read("FilterClassIntersections.g");
Read("InverseClassCompression.g");

#This file handles the logic behind searching for and filtering feasible class intersections, after being given a modular intersection list.
#For a description of the algorithm, see PAPER.



####################################################################################################################


MakeSpaceList := function(partn_ceiling, len)
	local
	partn_space_lst,
	sum,
	i, j;

	partn_space_lst := EmptyPlist(len);

	for i in [1.. len] do
		sum := 0;

		for j in [i.. len] do
			sum := sum + partn_ceiling[j];
		od;

		partn_space_lst[i] := sum;
	od;

	partn_space_lst := Concatenation(partn_space_lst, [0]); #When doing IteratePartition, this accounts for the idx = len case

	return partn_space_lst;
end;


PartitionCeiling := function(ceiling, partn_posns_lst, len)
	local
	partn_ceilings,
	i, j;

	partn_ceilings := EmptyPlist(Length(partn_posns_lst));

	for i in [1.. Length(partn_posns_lst)] do
		partn_ceilings[i] := ListWithIdenticalEntries(len, 0);

		for j in partn_posns_lst[i] do
			partn_ceilings[i][j] := ceiling[j];
		od;
	od;

	return partn_ceilings;
end;


PartitionSpaceLists := function(partn_ceilings, len)
	local partn_ceiling, partn_space_lsts;

	partn_space_lsts := [];

	for partn_ceiling in partn_ceilings do
		Append(partn_space_lsts, [ MakeSpaceList(partn_ceiling, len) ] );
	od;

	return partn_space_lsts;
end;


####################################################################################################################

StackCeiling := function(ceiling, partn_posns_lst, num_partns)
	local stack_ceiling, i;

	stack_ceiling := EmptyPlist(num_partns);

	for i in [1.. num_partns] do
		stack_ceiling[i] := Sum( ceiling{partn_posns_lst[i]} );
	od;

	return stack_ceiling;
end;


PartitionsOfK := function(k, ceiling, partn_posns_lst, partn_moduli_lst)
	local
	num_partns,
	partns_k,
	lst, stack_ceiling, partn_space_lst,
	space_lst,
	zeroes,
	finished;

	partns_k := [];

	num_partns := Length(partn_moduli_lst);
	zeroes := ListWithIdenticalEntries(num_partns, 0);

	stack_ceiling := StackCeiling(ceiling, partn_posns_lst, num_partns);
	space_lst := MakeSpaceList(stack_ceiling, num_partns);
	lst := ShallowCopy(zeroes);
	PlaceStack(lst, stack_ceiling, k, 1, num_partns);

	finished := false;

	while not finished do
		if lst mod partn_moduli_lst = zeroes then
			Append(partns_k, [ ShallowCopy(lst) ]);
		fi;

		finished := IteratePartition(lst, stack_ceiling, space_lst, num_partns);
	od;

	return partns_k;
end;


####################################################################################################################


ModuliClassPartition := function(moduli, partn_moduli_lst)
	local partn_posns_lst, x;

	partn_posns_lst := [];

	for x in partn_moduli_lst do
		Append(partn_posns_lst, [Positions(moduli, x)]);
	od;

	return partn_posns_lst;
end;


####################################################################################################################

SearchClassIntersections := function(pds_data, min_cl_ints, filtr_mat, moduli)
	local 
	ceiling,
	len,
	partn_moduli_lst, partn_posns_lst, partn_ceilings, partn_space_lsts,
	partns_k;

	len := Length(min_cl_ints);
	ceiling := List(pds_data.cls, Size);

	partn_moduli_lst := Unique(moduli);
	partn_posns_lst := ModuliClassPartition(moduli, partn_moduli_lst);
	partn_ceilings := PartitionCeiling(ceiling, partn_posns_lst, len);
	partn_space_lsts := PartitionSpaceLists(partn_ceilings, len);

	partns_k := PartitionsOfK(pds_data.k, ceiling, partn_posns_lst, partn_moduli_lst);
end;
