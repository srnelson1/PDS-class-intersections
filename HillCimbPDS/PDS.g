Read("GroupRing.g");

SortConj := function(conj_classes)
    local size_list, class;

    size_list := List(conj_classes, class -> Size(class));
    SortParallel(size_list, conj_classes);
end;

#Generates an inverse closed PDS with conj class intersection given by vec. Takes as input group, vec, convolution_table, or just group,vec
RandomDFromVec := function(args...)
    local convolution_table, group, vec, conj_classes, i, D_class_intersect, random_element, inverse_element, l, D;

    if Size(args) = 2 then
        convolution_table := ConvolutionTable(args[1]);
        vec := args[2];
    else
        convolution_table := args[2];
        vec := args[3];
    fi;

    group := args[1];

    #Convert conj_classes from basis representation to list of elements
    conj_classes := List(ConjugacyClasses(group), i -> BasisElements(InGroupRing(group, i)));
    D_class_intersect := List([1..Length(conj_classes)], i -> []);

    SortConj(conj_classes); #This is a hacked solution that should NOT be in the final build. It makes sure vec and conj_classes indices align
    Sort(vec);

    for i in [1..Length(conj_classes)] do

        while Length(D_class_intersect[i]) < vec[i] do
            random_element := Random(conj_classes[i]); #Get random element
            Append(D_class_intersect[i], [random_element]);
            Remove(conj_classes[i], Position(conj_classes[i], random_element));

            inverse_element := FindInverse(convolution_table, random_element);

            if not inverse_element = random_element then
                l := Filtered([1..Length(conj_classes)], l ->  inverse_element in conj_classes[l]);
                l := l[1];

                Append(D_class_intersect[l], [inverse_element]);
                Remove(conj_classes[l], Position(conj_classes[l], inverse_element));
            fi;
        od;
    od;


    D := [1..Size(group)] * 0;

    for i in Flat(D_class_intersect) do
        D[i] := 1;
    od;

    return D;
end;

#Finds group ring representation of D^2
CalculateDSquared := function(convolution_table, D)
    local order, D_elements, i, j, D_squared;

    order := DimensionsMat(convolution_table)[1];

    D_elements := Filtered(List([1..order], i -> i*D[i]), j -> j <> 0);
    D_squared := [1..order] * 0;

    for i in D_elements do
        for j in D_elements do
            D_squared[convolution_table[i][j]] := D_squared[convolution_table[i][j]] + 1;
        od;
    od;

    return D_squared;
end;

#Given convolution_table, D, params, checks if D^2 = (k-mu)*e + (lambda-mu)*D + mu*G
CalculatePDSProximity := function(convolution_table, D, params)
    local k, lambda, mu, D_squared, order, e, G;

    k := params[2];
    lambda := params[3];
    mu := params[4];

    D_squared := CalculateDSquared(convolution_table, D);

    order := DimensionsMat(convolution_table)[1];
    e := List([1..order], i -> 0);
    e[1] := 1;

    G := List([1..order], i -> 1);

    return (D_squared+(mu-lambda)*D+(mu-k)*e - mu*G)^2;
end;
