Read("SwartzTauschekRestriction.g");
Read("SearchClassIntersections.g");
Read("PreliminaryIntersections.g");


BuildPDSData := function(group, v, k, lambda, mu)
	local char_table, irr,
	row, x;

	if IsList(group) then
		group := SmallGroup(group);
	fi;

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
		theta1 := (lambda - mu + RootInt((lambda - mu)^2 + 4*(k - mu), 2))/2,
		theta2 := (lambda - mu - RootInt((lambda - mu)^2 + 4*(k - mu), 2))/2
	);
end;


#Finds possible PDS Class Intersection of a particular group.
PDSClassIntersections := function(group, v, k, lambda, mu)
	local
	pds_data, min,
	min_cl_ints, cl_ints_lst;

	if not STRestriction(group, v, k, lambda, mu) then
		return [];
	fi;

	pds_data := BuildPDSData(group, v, k, lambda, mu);
	min := MinimalIntersections(pds_data);

	cl_ints_lst := [];

	for min_cl_ints in min.cl_ints_lst do
		Append(cl_ints_lst, AllClassIntersections(pds_data, min_cl_ints, min.moduli));
	od;

	return cl_ints_lst;
end;

