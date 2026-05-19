Read("SwartzTauschekRestriction.g");
Read("SearchClassIntersections.g");
Read("MinimalIntersections.g");


BuildPDSData := function(group, params)
	local
	v, k, lambda, mu,
	char_table, irr,
	theta1, theta2,
	row, x;

	if IsList(group) then
		group := SmallGroup(group);
	fi;

	v := params[1]; k := params[2]; lambda := params[3]; mu := params[4];
	theta1 := (lambda - mu + RootInt((lambda - mu)^2 + 4*(k - mu), 2))/2;
	theta2 := (lambda - mu - RootInt((lambda - mu)^2 + 4*(k - mu), 2))/2;

	char_table := CharacterTable(group);
	irr := Irr(char_table); # We guarantee ordering is based on char_table

	return rec(
		group := group,
		char_table := char_table,
		irr := irr, 
		char_mat := List(irr, row -> List(row, x -> x)),
		cls := ConjugacyClasses(char_table),
		v := v,
		k := k,
		theta1 := theta1,
		theta2 := theta2,
		cp_delta := Product( Filtered( PrimeDivisors( theta1-theta2), x -> v mod x <> 0 ) )
	);
end;

#Finds possible PDS Class Intersection of a particular group.
PDSClassIntersections := function(group, params)
	local
	pds_data,
	min_lst, min,
	cl_ints_lst;

	if IsList(group) then
		group := SmallGroup(group);
	fi;

	if not STRestriction(group, params) then
		return [];
	fi;

	pds_data := BuildPDSData(group, params);
	min_lst := MinimalIntersections(pds_data);


	cl_ints_lst := [];

	for min in min_lst do
		Append(cl_ints_lst, AllClassIntersections(pds_data, min));
	od;

	return cl_ints_lst;
end;

