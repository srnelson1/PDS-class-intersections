#This file handles doing computations in group rings. GAP has group ring functionality with its own uses, but when
#doing intensive computations concerning group ring elements, utilizing the convolution table and representing sets as
#lists is faster.

#I wrote ConvolutionTable, inspired by Ken Smith at (kenwsmith54@gmail.com). This code generates convolution tables for groups
#up to order 1000 in <= 1 sec
ConvolutionTable := function(group)
    local order, elements, convolution_table, i, j;

    order := Size(group);
    elements := Elements(group);
    convolution_table := List([1..order], i -> []);

    for i in [1..order] do 
        for j in [1..order] do
            convolution_table[i][j] := Position(elements, elements[i]*elements[j]);
        od; 
    od;

    return convolution_table;
end;

#returns group_obj as group ring representation
InGroupRing := function(group, group_obj) #Takes in a subset {s_1, ..., s_n} of a group G, and returns a 0,1-vector with 1 in position k whenever elements[k] = s_r for some r.
    local elements, group_ring_obj, element, k;

    elements := Elements(group);
    group_ring_obj := ListWithIdenticalEntries(Length(elements), 0);

    for element in group_obj do
        k := Position(elements, element);
        group_ring_obj[k] := group_ring_obj[k] + 1;
    od;

    return group_ring_obj;
end;

#Returns inverse of an element based on convolution_table
FindInverse := function(convolution_table, element_index)
    local i;

    for i in convolution_table[element_index] do
        if convolution_table[element_index][i] = 1 then
            return i;
        fi;
    od;
end;

#Given ring objects returns the basis elements of the ring object. This object may be a multiset.
BasisElements := function(list)
    local i, elements;
    elements := [];

    for i in [1..Length(list)] do
        if list[i] <> 0 then
            Append(elements, [i]);
        fi;
    od;

    return elements;
end;


ConjClasses := function(group)
    local conj_class;
    return List(ConjugacyClasses(group), conj_class -> BasisElements(InGroupRing(group, conj_class)));
end;
