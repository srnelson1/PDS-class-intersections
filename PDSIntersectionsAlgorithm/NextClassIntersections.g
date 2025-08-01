

LastNonzeroIdx := function(lst, partn_ceiling, len)
	local i;

	i := len;

	while i > 0 do
		if lst[i] <> 0 and partn_ceiling[i] <> 0 then
			return i;
		fi;

		i := i - 1;
	od;

	return -1;
end;


NextNonzeroCeilingIdx := function(partn_ceiling, idx, len)
	local i;

	for i in [idx.. len] do
		if partn_ceiling[i] <> 0 then
			return i;
		fi;
	od;

	return -1;
end;


MoveUpOne := function(lst, partn_ceiling, idx, len)
	local j;

	j := NextNonzeroCeilingIdx(partn_ceiling, idx + 1, len);

	lst[idx] := lst[idx] - 1;
	lst[j] := 1;

	return j + 1;
end;


PlaceStack := function(lst, partn_ceiling, stack, idx, len)
	local j;

	for j in [idx.. len] do
		if partn_ceiling[j] <> 0 then
			if stack > partn_ceiling[j] then
				lst[j] := partn_ceiling[j];
				stack := stack - partn_ceiling[j];
			else
				lst[j] := stack;
				break;
			fi;
		fi;
	od;
end;



RebuildList := function(lst, partn_ceiling, partn_space_lst, idx, len)
	local
	stack,
	x,
	i;

	stack := 0;

	while true do
		i := LastNonzeroIdx(lst, partn_ceiling, len);

		if i = -1 then
			return true;
		fi;

		stack := stack + 1;
		lst[i] := lst[i] - 1;

		if stack <= partn_space_lst[i+1] then
			break;
		fi;
	od;

	PlaceStack(lst, partn_ceiling, stack, i + 1, len);

	return false;
end;


IteratePartition := function(lst, partn_ceiling, partn_space_lst, len)
	local
	finished,
	idx;

	finished := false;
	idx := LastNonzeroIdx(lst, partn_ceiling, len);

	if idx = -1 then
		finished := true;
	elif (partn_space_lst[idx + 1] <> 0) then
		MoveUpOne(lst, partn_ceiling, idx, len);
	else
		finished := RebuildList(lst, partn_ceiling, partn_space_lst, idx, len);
	fi;

	return finished;
end;


######################################################################################################################################


ResetList := function(lst, base_lst, partn_posns)
	local j;

	for j in partn_posns do
		lst[j] := base_lst[j];
	od;
end;


NextClassIntersection := function(lst, base_lst, partn_ceiling_lst, partn_space_lsts, partn_posns_lst, len, cycles)
	local finished, i;

	i := 1;

	finished := IteratePartition(lst, partn_ceiling_lst[i], partn_space_lsts[i], len);


	while finished do
		ResetList(lst, base_lst, partn_posns_lst[i]);
		i := i + 1;

		if i = cycles + 1 then
			return true;
		fi;

		finished := IteratePartition(lst, partn_ceiling_lst[i], partn_space_lsts[i], len);
	od;

	return false;
end;
