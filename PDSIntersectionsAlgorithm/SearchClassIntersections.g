Read("NextClassIntersections.g");
Read("FilterClassIntersections.g");

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
	partn_ceiling_lst,
	i, j;

	partn_ceiling_lst := EmptyPlist(Length(partn_posns_lst));

	for i in [1.. Length(partn_posns_lst)] do
		partn_ceiling_lst[i] := ListWithIdenticalEntries(len, 0);

		for j in partn_posns_lst[i] do
			partn_ceiling_lst[i][j] := ceiling[j];
		od;
	od;

	return partn_ceiling_lst;
end;


PartitionSpaceLists := function(partn_ceiling_lst, len)
	local partn_ceiling, partn_space_lsts;

	partn_space_lsts := [];

	for partn_ceiling in partn_ceiling_lst do
		Append(partn_space_lsts, [ MakeSpaceList(partn_ceiling, len) ] );
	od;

	return partn_space_lsts;
end;


####################################################################################################################

NormalizeModSums := function(mod_sums_lst, partn_moduli_lst)
	local i, j;

	for i in [1.. Length(mod_sums_lst)] do
		for j in [1.. Length(mod_sums_lst[i])] do
			mod_sums_lst[i][j] := Int( mod_sums_lst[i][j] / partn_moduli_lst[j] );
		od;
	od;

	return mod_sums_lst;
end;

StackCeiling := function(ceiling, partn_posns_lst, num_partns)
	local stack_ceiling, i;

	stack_ceiling := EmptyPlist(num_partns);

	for i in [1.. num_partns] do
		stack_ceiling[i] := Sum( ceiling{partn_posns_lst[i]} );
	od;

	return stack_ceiling;
end;


ModSumsOfK := function(k, ceiling, partn_posns_lst, partn_moduli_lst)
	local
	num_partns,
	mod_sums_lst,
	lst, stack_ceiling, partn_space_lst,
	space_lst,
	zeroes,
	finished;

	mod_sums_lst := [];

	num_partns := Length(partn_moduli_lst);
	zeroes := ListWithIdenticalEntries(num_partns, 0);

	stack_ceiling := StackCeiling(ceiling, partn_posns_lst, num_partns);
	space_lst := MakeSpaceList(stack_ceiling, num_partns);
	lst := ShallowCopy(zeroes);
	PlaceStack(lst, stack_ceiling, k, 1, num_partns);

	finished := false;

	while not finished do
		if lst mod partn_moduli_lst = zeroes then
			Append(mod_sums_lst, [ ShallowCopy(lst) ]);
		fi;

		finished := IteratePartition(lst, stack_ceiling, space_lst, num_partns);
	od;

	return NormalizeModSums(mod_sums_lst, partn_moduli_lst);
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


BuildList := function(mod_sum, partn_ceiling_lst, len)
	local lst, i;

	lst := ListWithIdenticalEntries(len,  0);

	for i in [1.. Length(mod_sum)] do
		PlaceStack(lst, partn_ceiling_lst[i], mod_sum[i], 1, len);
	od;

	return lst;
end;


####################################################################################################################


SearchClassIntersections := function(pds_data, min_cl_ints, filtr_mat, moduli)
	local 
	ceiling,
	len,
	partn_moduli_lst, partn_posns_lst, partn_ceiling_lst, partn_space_lsts,
	mod_sums_lst, mod_sum,
	lst, base_lst,
	finished,
	cycles;

	ceiling := List(pds_data.cls, Size);
	len := Length(ceiling);

	partn_moduli_lst := Unique(moduli);
	partn_posns_lst := ModuliClassPartition(moduli, partn_moduli_lst);
	partn_ceiling_lst := PartitionCeiling(ceiling, partn_posns_lst, len);
	partn_space_lsts := PartitionSpaceLists(partn_ceiling_lst, len);

	cycles := Length(partn_moduli_lst);

	mod_sums_lst := ModSumsOfK(pds_data.k - Sum(min_cl_ints), ceiling, partn_posns_lst, partn_moduli_lst);

	for mod_sum in mod_sums_lst do
		lst := BuildList(mod_sum, partn_ceiling_lst, len);
		base_lst := ShallowCopy(lst);

		finished := false;

		while not finished do 
			finished := NextClassIntersection(lst, base_lst, partn_ceiling_lst, partn_space_lsts, partn_posns_lst, len, cycles);
			Print(lst);
		od;
	od;

end;
