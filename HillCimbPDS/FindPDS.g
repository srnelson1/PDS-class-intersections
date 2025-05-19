Read("PDS.g");
Read("GroupRing.g");


SwapG := function(convolution_table, D, g, g_inverse)
    local order, g_term, gD_Dg, i, Dg, gD;

    order := Length(convolution_table);
    
    g_term := [1..order] * 0;
    gD_Dg := [];

    if g <> g_inverse then
        g_term[1] := 2; #this computes 2*g*g^-1
        g_term[convolution_table[g_inverse][g_inverse]] := 1;
        g_term[convolution_table[g][g]] := 1;

        for i in D do
            g_term[convolution_table[g][i]] := g_term[convolution_table[g][i]]-1;
            g_term[ convolution_table[i][g]] := g_term[ convolution_table[i][g]]-1;
            g_term[convolution_table[g_inverse][i]] := g_term[convolution_table[g_inverse][i]]-1;
            g_term[convolution_table[i][g_inverse]] := g_term[convolution_table[i][g_inverse]]-1;
        od;
    else
        g_term[1] := 1;

        for i in D do
            g_term[convolution_table[g][i]] := g_term[convolution_table[g][i]]-1;
            g_term[convolution_table[i][g]] := g_term[convolution_table[i][g]]-1;
        od;
    fi;

    return g_term;
end;

SwapH := function(convolution_table, D, g, g_inverse, h, h_inverse)
    local h_term, i;

    h_term := [1..Length(convolution_table)] * 0;

    if h <> h_inverse then
        h_term[1] := 2; #this computes 2*h*h^-1
        h_term[convolution_table[h_inverse][h_inverse]] := 1;
        h_term[convolution_table[h][h]] := 1;

        h_term[convolution_table[g][h]] := -1; #This block is -(g + g^-1)*(h + h^-1) - (h + h^-1)*(g + g^-1)
        h_term[convolution_table[h][g]] := h_term[convolution_table[h][g]]-1;
        h_term[convolution_table[g_inverse][h]] := -1;
        h_term[convolution_table[h][g_inverse]] :=h_term[convolution_table[h][g_inverse]]-1;
        h_term[convolution_table[g][h_inverse]] := -1;
        h_term[convolution_table[h_inverse][g]] :=   h_term[convolution_table[h_inverse][g]]-1;
        h_term[convolution_table[h_inverse][g_inverse]] := -1;
        h_term[convolution_table[g_inverse][h_inverse]] :=h_term[convolution_table[g_inverse][h_inverse]]-1;

        for i in D do
            h_term[convolution_table[h][i]] := h_term[convolution_table[h][i]]+1;
            h_term[convolution_table[i][h]] := h_term[convolution_table[i][h]]+1;
            h_term[convolution_table[h_inverse][i]] := h_term[convolution_table[h_inverse][i]]+1;
            h_term[convolution_table[i][h_inverse]] := h_term[convolution_table[i][h_inverse]]+1;
        od;
    else
        h_term[1] := 1;
        h_term[convolution_table[g][h]] := -1;
        h_term[convolution_table[h][g]] := h_term[convolution_table[h][g]]-1;

        for i in D do
            h_term[convolution_table[h][i]] := h_term[convolution_table[h][i]]+1;
            h_term[convolution_table[i][h]] := h_term[convolution_table[i][h]]+1;
        od;
    fi;

    return h_term;
end;

SearchPDS := function(group, convolution_table, vec, params)
    local tempD_elements, g_swap, best_squared, test_D_squared, g_inverse, h_inverse, e, k, lambda, mu, order, tempD_squared, test_error, G, test, tempD, newD, i, best, cache_elements, conj, g, h, conjg, error, compD, bestneigh, besterror;


    conj := ConjClasses(group);
    tempD := RandomDFromVec(group, convolution_table, vec);
    tempD_elements := BasisElements(tempD);
    best := CalculatePDSProximity(convolution_table, tempD, params);
    tempD_squared := CalculateDSquared(convolution_table, tempD);

    order := Size(group);

    e := [1..order] * 0;
    e[1] := 1;
    G := List([1..order], i -> 1);
    k := params[2];
    lambda := params[3];
    mu := params[4];

    if best = 0 then
        return [tempD, best];
    else
        test:= false;
    fi;
    
    while not test do
        besterror:= best;
        cache_elements := [];
        

        for g in tempD_elements do
            if not g in cache_elements then
                conjg:= Filtered(conj, i -> g in i)[1];
                compD:= Filtered([1..Size(group)], i -> not i in tempD_elements);
                g_inverse := FindInverse(convolution_table, g);
                g_swap := SwapG(convolution_table, tempD_elements, g, g_inverse);

                for h in Intersection(conjg, compD) do	
                    newD:= ShallowCopy(tempD);
                    newD[g] := 0 ;
                    newD[h] := 1;
                    h_inverse := FindInverse(convolution_table, h);
                    newD[g_inverse] := 0;
                    newD[h_inverse] := 1;

                    test_D_squared := tempD_squared + g_swap;
                    test_D_squared := test_D_squared + SwapH(convolution_table, tempD_elements, g, g_inverse, h, h_inverse);
                   
                    error := (test_D_squared + (mu-lambda)*newD+(mu-k)*e - mu*G)^2;

                    if error = 0 then
                        test:= true;
                        return [newD, error];
                    fi;
                    if error < besterror then
                        besterror:= error;
                        bestneigh:= newD;
                        best_squared := test_D_squared;
                    fi;
                od;
            fi;
            Append(cache_elements, [FindInverse(convolution_table, g)]); #We cache the inverse of g, since already considered
        od;
        if besterror < best then
            tempD:= bestneigh;
            tempD_squared := best_squared;
            tempD_elements := BasisElements(tempD);
            best:= besterror;
        else
            test:= true;	
        fi;		
    od;

    return [tempD, best];
end;

RandomSearchPDS := function(group, vec, params, args...)
    local check_trials, number_trials, convolution_table, l, tempD, best, trials;

    check_trials := false;

    if Size(args) = 1 then
        number_trials := args[4];
        check_trials := true;
    fi;

    convolution_table := ConvolutionTable(group);
    l:= SearchPDS(group, convolution_table, vec, params);

    tempD:= l[1];
    best:= l[2];

    trials:= 1;
    Print(String(trials), "     ", String(best), "\n");
    while best > 0 do
        l:= SearchPDS(group, convolution_table, vec, params);
        if l[2] < best then
            tempD:= l[1];
            best:= l[2];
        fi;
        trials:= trials + 1;
        Print(String(trials), "     ", String(best), "\n");


        if check_trials then
            if trials >= number_trials then
                break;
            fi;
        fi;
    od;

    return [tempD, best];
end;

RandomSearchPDSFile := function(group, vec, params, file, args...)
    local check_trials, convolution_table, number_trials, l, tempD, best, trials;

    check_trials := false;

    if Size(args) = 1 then
        number_trials := args[5];
        check_trials := true;
    fi;

    convolution_table := ConvolutionTable(group);
    l:= SearchPDS(group, convolution_table, vec, params);

    tempD:= l[1];
    best:= l[2];

    trials:= 1;

    while best > 0 do
        l:= SearchPDS(group, convolution_table, vec, params);
        if l[2] < best then
            tempD:= l[1];
            best:= l[2];
        fi;
        trials:= trials + 1;
        if trials mod 10 = 0 then
            AppendTo(file, trials, "   ",best, "\n");
        fi;

        if check_trials then
            if trials >= number_trials then
                break;
            fi;
        fi;
    od;

    AppendTo(file, [tempD, best]);
end;
