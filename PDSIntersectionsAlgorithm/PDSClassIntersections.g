Read("GeneralCoprimeRelations.g");
Read("SearchClassIntersections.g");
Read("PreliminaryIntersections.g");


CharMatrix := function(irr) #Converts group or character table into a matrix of characters
	local row, i;
	return List(irr, row -> List(row, i -> i)); #return matrix of characters.
end;

#Finds possible PDS Class Intersection of a particular group.
PDSClassIntersectionsGroup := function(group, v, k, lambda, mu)
	local
	pds_data,
	char_table, irr,
	prelim_result, final_result,
	min_cl_ints, min_cl_ints_lst, moduli,
	cl_ints_lst,
	x;

	if IsList(group) then
		group := SmallGroup(group);
	fi;

	char_table := CharacterTable(group);
	irr := Irr(char_table);

	pds_data := rec( #This record contains all the necessary information about the group and possible pds.
		group := group,
		char_table := char_table,
		char_mat := CharMatrix(irr),
		cls := ConjugacyClasses(char_table),
		irr := irr, 
		v := v,
		k := k,
		theta1 := (lambda - mu + RootInt((lambda - mu)^2 + 4*(k - mu), 2))/2,
		theta2 := (lambda - mu - RootInt((lambda - mu)^2 + 4*(k - mu), 2))/2
	);

	final_result := rec();
	if prelim_result.successful then
		for min_cl_ints in min_cl_ints_lst do
			Append(cl_ints_lst, AllClassIntersections(pds_data, min_cl_ints, moduli));
		od;
	else
		cl_ints_lst := [];
		final_result.fail_reason := prelim_result.fail_reason;
	fi;


	final_result.cl_ints_lst := cl_ints_lst;
	final_result.moduli := moduli;
	final_result.min_cl_ints_lst := prelim_result.min_cl_ints_lst;
	final_result.successful := cl_ints_lst <> [];


	if final_result.successful then
		final_result.fail_reason := "None";

	elif prelim_result.successful = false then
		final_result.fail_reason := "No Valid Class Intersections";
	fi;

	final_result.params := [v, k, lambda, mu];

	return final_result;
end;

#This pulls all possible groups on the parameter set [v, k, lambda, mu]. It finds a possible PDS class intersection for each group
PDSClassIntersections := function(v, k, lambda, mu)
	local groups, group, class_intersection, i, number_groups, possible_pds_lst, x;

	groups := FindCoprimeGroups(v, k, lambda, mu);

	if Length(groups) = 0 then
		class_intersection := rec(fail_reason := "No groups on this order", successful := false);
	fi;

	number_groups := Length(groups);
	possible_pds_lst := EmptyPlist(number_groups);

	for i in [1.. number_groups] do
		group := groups[i];
		class_intersection := PDSClassIntersectionsGroup(group, v, k, lambda, mu);
		class_intersection.group := IdGroup(group);
		possible_pds_lst[i] := class_intersection;
	od;

	return possible_pds_lst;
end;
