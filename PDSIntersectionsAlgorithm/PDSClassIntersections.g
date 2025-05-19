Read("GeneralCoprimeRelations.g");
Read("SearchClassIntersections.g");
Read("PreliminaryIntersections.g");


CharMatrix := function(char_table) #Converts group or character table into a matrix of characters
    local row, i;
    return List(Irr(char_table), row -> List(row, i -> i)); #return matrix of characters.
end;

#Finds possible PDS Class Intersection of a particular group.
PDSClassIntersectionsGroup := function(group, v, k, lambda, mu)
    local
    group_param_rec,
    char_table,
    prelim_result, final_result,
    prelim_cl_intersections, prelim_cl_intersections_list, moduli,
    cl_intersections_list,
    x;

    if IsList(group) then
        group := SmallGroup(group);
    fi;

    char_table := CharacterTable(group);

    group_param_rec := rec( #This record contains all the necessary information about the group and possible pds.
        group := group,
        char_table := char_table,
        char_mat := CharMatrix(char_table),
        cls := ConjugacyClasses(char_table),
        v := v,
        k := k,
        theta1 := (lambda - mu + RootInt((lambda - mu)^2 + 4*(k - mu), 2))/2,
        theta2 := (lambda - mu - RootInt((lambda - mu)^2 + 4*(k - mu), 2))/2
    );

    final_result := rec();
    prelim_result := PreliminaryIntersections(group_param_rec);
    moduli := prelim_result.moduli;
    cl_intersections_list := [];

    if prelim_result.successful then
        prelim_cl_intersections_list := prelim_result.prelim_cl_intersections_list;


        for prelim_cl_intersections in prelim_cl_intersections_list do
            x := AllClassIntersections(group_param_rec, prelim_cl_intersections, moduli);
            Append(cl_intersections_list, x );
        od;
    else
        cl_intersections_list := [];
        final_result.fail_reason := prelim_result.fail_reason;
    fi;


    final_result.cl_intersections_list := cl_intersections_list;
    final_result.moduli := moduli;
    final_result.prelim_cl_intersections_list := prelim_result.prelim_cl_intersections_list;
    final_result.successful := cl_intersections_list <> [];


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
    local groups, group, class_intersection, i, number_groups, possible_pds_list, x;

    groups := FindCoprimeGroups(v, k, lambda, mu);

    if Length(groups) = 0 then
        class_intersection := rec(fail_reason := "No groups on this order", successful := false);
    fi;

    number_groups := Length(groups);
    possible_pds_list := EmptyPlist(number_groups);

    for i in [1.. number_groups] do
        group := groups[i];
        class_intersection := PDSClassIntersectionsGroup(group, v, k, lambda, mu);
        class_intersection.group := IdGroup(group);
        possible_pds_list[i] := class_intersection;
    od;

    return possible_pds_list;
end;