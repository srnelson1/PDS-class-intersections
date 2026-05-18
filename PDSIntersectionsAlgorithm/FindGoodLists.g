

LastNonzeroIdx := function(lst, partn, len)
	local i;

	i := len;

	while i > 0 do
		if lst[i] <> 0 and partn.ceiling[i] <> 0 then
			return i;
		fi;

		i := i - 1;
	od;

	return -1;
end;


NextNonzeroCeilingIdx := function(partn, idx, len)
	local i;

	for i in [idx.. len] do
		if partn.ceiling[i] <> 0 then
			return i;
		fi;
	od;

	return -1;
end;


MoveUpOne := function(lst, partn, idx, len)
	local j;

	j := NextNonzeroCeilingIdx(partn, idx + 1, len);

	lst[idx] := lst[idx] - 1;
	lst[j] := 1;

	return j + 1;
end;


PlaceStack := function(lst, partn, stack, idx, len)
	local j;

	for j in [idx.. len] do
		if partn.ceiling[j] <> 0 then
			if stack > partn.ceiling[j] then
				lst[j] := partn.ceiling[j];
				stack := stack - partn.ceiling[j];
			else
				lst[j] := stack;
				break;
			fi;
		fi;
	od;
end;


RebuildList := function(lst, partn, idx, len)
	local
	stack,
	i;

	stack := 0;

	while true do
		i := LastNonzeroIdx(lst, partn, len);

		if i = -1 then
			return true;
		fi;

		stack := stack + 1;
		lst[i] := lst[i] - 1;

		if stack <= partn.space_lst[i+1] then
			break;
		fi;
	od;

	PlaceStack(lst, partn, stack, i + 1, len);

	return false;
end;


IteratePartition := function(lst, partn, len)
	local
	finished,
	idx;

	finished := false;
	idx := LastNonzeroIdx(lst, partn, len);

	if idx = -1 then
		finished := true;
	elif (partn.space_lst[idx + 1] <> 0) then
		MoveUpOne(lst, partn, idx, len);
	else
		finished := RebuildList(lst, partn, idx, len);
	fi;

	return finished;
end;


######################################################################################################################################


ResetList := function(lst, base_lst, posns)
	local j;

	for j in posns do
		lst[j] := base_lst[j];
	od;
end;


NextList := function(lst, base_lst, partn, len, cycles)
	local finished, i;

	i := 1;

	partn.ceiling := partn.ceiling_lst[i];
	partn.space_lst := partn.space_lsts[i];
	finished := IteratePartition(lst, partn, len);

	while finished do
		ResetList(lst, base_lst, partn.posns_lst[i]);
		i := i + 1;

		if i = cycles + 1 then
			return true;
		fi;

		partn.ceiling := partn.ceiling_lst[i];
		partn.space_lst := partn.space_lsts[i];
		finished := IteratePartition(lst, partn, len);
	od;

	return false;
end;


FindGoodLists := function(base_lst, partn, fltr_func)
	local
	len,
	cycles,
	finished,
	lst,
	good_lsts;

	len := Length(base_lst);
	cycles := Length(partn.posns_lst);

	good_lsts := [];
	lst := ShallowCopy(base_lst);

	finished := false;

	while not finished do
		if fltr_func(lst) then
			Add(good_lsts, ShallowCopy(lst));
		fi;

		finished := NextList(lst, base_lst, partn, len, cycles);
	od;

	return good_lsts;
end;
