
#The purpose of this file is to take the set of prelim_cl_intersections and build all class intersections, called cl_intersections,
#satisfying the restriction that cl_intersections[i] = prelim_cl_intersections[i] mod moduli[i].

#For a description of the algorithm, see PAPER.


##############################################################################################################
####LIST GENERATION###########################################################################################

#This section is dedicated to generating all lists. The code is built to generate a list in linear order
#in the sense that beginning with a starting list, cl_intersections, we repeatedly apply NextClassIntersection
#to cl_intersections, and generate all possible lists without backtracking.

#We achieve this behavior subject to two constraints, each list must sum to an identical quantity called stack_size,
#and the ith position in each list is strictly bounded by some value specified in ceiling[i] (the interpretation for
#these values is given in AllClassIntersections). So, we initialize by entering a stacks_list [a_1, ..., a_r] such that 
#j is the smallest value for which a_j, ..., a_r = 0, respecting the constraint Sum(stacks_list) = stack_size and
#a_i <= ceiling[i]. Psuedo code is given for the main process above NextClassIntersection.

RightmostNonzeroPosition := function(cl_intersections, partition_ceiling)
    local i, list_size;

    list_size := Size(cl_intersections);

    for i in [0..(list_size-1)] do
        if cl_intersections[list_size - i] <> 0 and cl_intersections[list_size-i] <= partition_ceiling[list_size-i] then
            return list_size - i;
            break;
        fi;
    od;

    return "All Zeroes";
end;

#If pickup_stack = max_stack, returns done. Otherwise, iterates through rightmost_pos..Size(stacks_list) and places as much of
#pickup_stack at rightmost_pos while respecting ceiling. if Sum(ceiling{[rightmost_pos..Size(stacks_list)]}) < pickup_stack and
#pickup_stack <> max_stack, then the above operation is impossible and we return Unplaceable.
PlaceStack := function(cl_intersections, partition_ceiling, rightmost_pos, pickup_stack, max_stack)
    local i, min_stack_ceil;

    if Sum(partition_ceiling{[rightmost_pos..Size(cl_intersections)]}) < pickup_stack then
        if pickup_stack = max_stack then
            return "Done";
        fi;

        return "Unplaceable";
    fi;

    for i in [rightmost_pos..Size(cl_intersections)] do
        min_stack_ceil := Minimum([pickup_stack, partition_ceiling[i]]);
        cl_intersections[i] := cl_intersections[i] + min_stack_ceil;
        
        if min_stack_ceil = pickup_stack then
            break;
        fi;

        pickup_stack := pickup_stack-min_stack_ceil;
    od;

    return cl_intersections;
end;

#Takes in a list [a_1, ..., a_n, 0, 0, ..., 0]. Initializes pickup_stack := 0. Then
#   1) Search for rightmost nonzero position, rightmost_pos.
#   2) Subtract 1 from rightmost_pos and add 1 to pickup_stack.
#   3) Search for next possible position in [rightmost_pos+1..end_of_list] to place pickup_stack which respects ceiling.
#   4) If no next position exists, check if pickup_stack contains all values of input list.
#   5) If yes, then quite, otherwise return to step 1.
NextClassIntersection := function(cl_intersections, partition_ceiling, stack_size, cl_intersections_length)
    local max_stack, list_size, check_placeable, rightmost_pos, pickup_stack, next_position;

    max_stack := stack_size;

    if RightmostNonzeroPosition(cl_intersections{[1..cl_intersections_length]}, partition_ceiling) = "All Zeroes" then
        return "Done";
    fi;

    pickup_stack := 0;
    check_placeable := "Unplaceable";

    while check_placeable = "Unplaceable" do
        rightmost_pos := RightmostNonzeroPosition(cl_intersections, partition_ceiling);

        if rightmost_pos = cl_intersections_length + 1 then #A slight deviation from algorithm. If rightmost_pos is at end of list then we move all of rightmost_pos into the stack, which saves some time
            pickup_stack := pickup_stack + cl_intersections[rightmost_pos];
            cl_intersections[rightmost_pos] := 0;
            rightmost_pos := RightmostNonzeroPosition(cl_intersections, partition_ceiling);
        fi;

        cl_intersections[rightmost_pos] := cl_intersections[rightmost_pos] - 1;
        pickup_stack := pickup_stack + 1;
        
        check_placeable := PlaceStack(cl_intersections, partition_ceiling, rightmost_pos + 1, pickup_stack, max_stack);
    od;

    if check_placeable = "Done" then
        return "Done";
    fi;

    return cl_intersections;
end;

##############################################################################################################
####INVERSE CLASS COMPRESSION#################################################################################
#Following from the fact that D^(-1) = D, we get |h^G \cap D| = | (h^-1)^G \cap D|. Thus, when we generate a class intersection,
#this class intersection must satisfy |h^G \cap D| = | (h^-1)^G \cap D| for all h^G. So, we instead compute our intersections by
#combining |(h^G \cup (h^G)^{-1]) \cap D|. If c, c' are the moduli corresponding h^G, (h^G)^{-1}, we set our new modulus
#for |(h^G \cup (h^G)^{-1]) \cap D| to c + c'. In practice, this means we have fewer intersections to search through with larger
#moduli, speeding up search times.

#For class representatives h_1, ..., h_n, return list of pairs [i, j] such that h_i^G = (h_j^G)^{-1}
IndexInverseClassList := function(reps, cls)
    local index_inv_cls_list, cl, inv_cl, x, i;

    index_inv_cls_list := [];

    for i in [1..Length(cls)] do
        cl := cls[i];

        inv_cl := Filtered(cls, x -> Inverse( reps[i] ) in x)[1];
        
        Append(index_inv_cls_list, [ [Position(cls, inv_cl), Position(cls, cl)] ]);
        Sort( Last(index_inv_cls_list) );
    od;

    index_inv_cls_list := Unique(index_inv_cls_list);
    Sort(index_inv_cls_list);

    return index_inv_cls_list;
end;

#For prelim_cl_intersections, ceiling, etc., we build new lists comb_prelim_cl_intersections, comb_ceiling, etc.
#which correspond to the combined intersections |(h^G \cup (h^G)^{-1]) \cap D|.
CombineInverseClasses := function(char_table, prelim_cl_intersections, ceiling, moduli, char_mat)
    local
    cl, cls, inv_cl,  ord_2_cls_list, elms_cl, elms_cl_list, reps,
    index_inv_cls_list, #list of elements [i, j] such that i is the index of the ith conjugacy class and j the index of its inverse
    comb_prelim_cl_intersections, #new prelim_cl_intersections such that index i 
    comb_ceiling,
    comb_char_mat,
    comb_moduli,
    x,
    i;

    cls := ConjugacyClasses(char_table);
    reps := List(cls, cl -> Representative(cl));
    ord_2_cls_list := List(reps, x -> Order(x) = 2);
    index_inv_cls_list := IndexInverseClassList(reps, cls);


    comb_prelim_cl_intersections := [];
    comb_ceiling := [];
    comb_moduli := [];
    comb_char_mat := [];


    char_mat := TransposedMat(char_mat);
    

    for i in [1..Length(index_inv_cls_list)] do
        if index_inv_cls_list[i][1] <> index_inv_cls_list[i][2] then
            comb_prelim_cl_intersections[i] := prelim_cl_intersections[index_inv_cls_list[i][1]] + prelim_cl_intersections[index_inv_cls_list[i][1]];
            comb_ceiling[i] := ceiling[index_inv_cls_list[i][1]] + ceiling[index_inv_cls_list[i][2]];
            comb_moduli[i] := moduli[index_inv_cls_list[i][1]] + moduli[index_inv_cls_list[i][2]];
            comb_char_mat[i] := (char_mat[index_inv_cls_list[i][1]] + char_mat[index_inv_cls_list[i][2]])/2; #Say index_inv_cls_list[k] = [i, j], then when we generate comb_cl_intersection, we want comb_char_mat[k] * comb_cl_intersection = char_mat[i] * cl_intersection + char_mat[j] * cl_intersection. This requires division by 2.
        else
            comb_prelim_cl_intersections[i] := prelim_cl_intersections[index_inv_cls_list[i][1]];
            comb_ceiling[i] := ceiling[index_inv_cls_list[i][1]];
            comb_moduli[i] := moduli[index_inv_cls_list[i][1]];
            comb_char_mat[i] := char_mat[index_inv_cls_list[i][1]];
        fi;
    od;

    comb_char_mat := TransposedMat(comb_char_mat);

    return  rec(
        comb_prelim_cl_intersections := comb_prelim_cl_intersections,
        index_inv_cls_list := index_inv_cls_list,
        comb_ceiling := comb_ceiling,
        comb_moduli := comb_moduli,
        comb_char_mat := comb_char_mat,
        ord_2_cls_list := ord_2_cls_list
        );
end;

#For those classes h^G satisfying h^G = h^{-1}^G but h <> h^{-1}, for which their modulus is odd, we enforce the modulus is even.
#See [NS] 4.6 (Thesis 6.6).
SelfInverseCombModuli := function(comb_prelim_cl_intersections, comb_moduli, index_inv_cls_list, ord_2_cls_list, v)
    local i;

    if v mod 2 = 0 then
        for i in [1..Length(index_inv_cls_list)] do
            if index_inv_cls_list[i][1] = index_inv_cls_list[i][2] then #If the class is its own inverse
                if ord_2_cls_list[i] = false then #but the elements of the class are not order 2
                    if comb_prelim_cl_intersections[i] mod 2 = 0 and comb_moduli[i] mod 2 = 1 then #then the intersection must be even
                        comb_moduli[i] := 2*comb_moduli[i];
                    fi;
                fi;
            fi;
        od;
    fi;

    return comb_moduli;
end;

#We uncombine all comb_cl_intersections in cl_intersections_list.
UncombineInverseClasses := function(cl_intersections_list, index_inv_cls_list)
    local
    cl_intersections,
    comb_cl_intersections,
    num_cls,
    index_inv_cls,
    i, j;

    num_cls := Length(Flat(index_inv_cls_list));

    for i in [1..Length(cl_intersections_list)] do
        comb_cl_intersections := cl_intersections_list[i];
        cl_intersections := EmptyPlist(num_cls);

        for j in [1..Length(index_inv_cls_list)] do
            index_inv_cls := index_inv_cls_list[j];
            
            if index_inv_cls[1] <> index_inv_cls[2] then
                cl_intersections[index_inv_cls[1]] := comb_cl_intersections[j]/2;
                cl_intersections[index_inv_cls[2]] := comb_cl_intersections[j]/2;
            else
                cl_intersections[index_inv_cls[1]] := comb_cl_intersections[j];
            fi;
        od;

        cl_intersections_list[i] := cl_intersections;
    od;

    return cl_intersections_list;
end;


##############################################################################################################
####INTERSECTION GENERATION###################################################################################
#This section

#We partition our set of combined classes H_1, ..., H_m into sets A_1, ..., A_n such that all classes inside each A_i have the same modulus.
#The partitions {A_i} are represented by the partition_positions list, in which partition_positions[i] consists of all integers k
#such that H_k \in A_i.
ModuliClassPartition := function(moduli)
    local partition_positions, x;

    partition_positions := [];

    for x in Unique(moduli) do
        Append(partition_positions, [Positions(moduli, x)]);
    od;

    return partition_positions;
end;

#We have partitioned our combined conjugacy classes into collections A_1, ..., A_n, such that all classes in A_i have the same
#modulus, which we denote as a_i. We now find and return all integer lists [c_1, ..., c_n] such that c_1 + ... + c_n = stack_size
#and c_i = 0 mod a_i.
PartitionStackSizes := function(partition_positions, moduli, partition_sum_ceiling, stack_size)
    local
    partition_stack_sizes, #This is a given set [c_1, ..., c_n]. It represents the possbile stack_size c_i for each partition A_i
    partition_stack_sizes_list, #This is the list of all sets [c_1, ..., c_n].
    zeroes,
    num_moduli,
    next_class_intersection,
    x;

    num_moduli := Length(partition_positions);
    moduli := Unique(moduli);
    zeroes := ListWithIdenticalEntries(num_moduli, 0);
    next_class_intersection := "Running";
    partition_stack_sizes_list := [];

    partition_stack_sizes := PlaceStack(ShallowCopy(zeroes), partition_sum_ceiling, 1, stack_size, stack_size + 1);

    while not next_class_intersection = "Done" do #We first generate all [c_1, ..., c_n] satisfying c_1 + ... + c_n = stack_size
        if partition_stack_sizes mod moduli = zeroes and partition_stack_sizes <= partition_sum_ceiling then #Then we check c_i = 0 mod a_i
            Append(partition_stack_sizes_list, [ShallowCopy(partition_stack_sizes)]);
        fi;

        next_class_intersection := NextClassIntersection(partition_stack_sizes, partition_sum_ceiling, stack_size, num_moduli-1);
    od;

    return partition_stack_sizes_list;
end;


#This is a recursive algorithm. We are given a list [c_1, ..., c_n] of partition_stack_sizes, a list of partition_positions
#for the partitions A_1, ..., A_n of combined classes, the comb_moduli of the combined classes classes, the ceiling of the 
#combined classes, and the number of combined classes, and we initialize a list partial_cl_intersections_list containing the
#zero list. Then, here is the pseudocode
#
#   redefine comb_moduli such that comb_moduli[j] equals the modulus of A_j.
#
#   for i in [1.. n]
#       for partial_comb_cl_intersections in partial_comb_cl_intersections_list
#           over all positions in partition_positions[i] (corresponding to the A_i partition), generate all updated_partial_comb_cl_intersections
#           satisfying Sum(updated_partial_comb_cl_intersections{partition_positions[i]}) = c_i/comb_moduli[i], and satisfying
#           updated_partial_comb_cl_intersections[j] = partial_comb_cl_intersections[j] whenever j is not in partition_positions[i].
#
#       Replace partial_comb_cl_intersections_list with the list of updated_partial_comb_cl_intersections
PartitionClassIntersectionsList := function(partition_positions, partition_stack_sizes, comb_moduli, ceiling, comb_cl_intersections_length)
    local
    partial_comb_cl_intersections_list, updated_partial_comb_cl_intersections_list,
    partial_comb_cl_intersections, updated_partial_comb_cl_intersections,
    partition_ceiling, zeroes,
    i;

    comb_moduli := Unique(comb_moduli); #Now comb_moduli[i] is the modulus of the classes in partition_positions[i]
    zeroes := ListWithIdenticalEntries(comb_cl_intersections_length+1, 0); #list of zeroes of length equal to number of combined classes

    partial_comb_cl_intersections_list := [ShallowCopy(zeroes)]; #Initialize the list which we iterate over.

    for i in PositionsProperty(partition_stack_sizes, x -> x <> 0) do #Iterate over indices of nonzero entries of partition_stack_sizes.
        updated_partial_comb_cl_intersections_list := []; #dummy list.
        partition_stack_sizes[i] := partition_stack_sizes[i]/comb_moduli[i]; #Normalizes partition_stack_sizes by the modulus. We later multiply all entries of partition_positions[i] by comb_moduli[i], guaranteeing we only generate intersections satisfying modular restriction

        for partial_comb_cl_intersections in partial_comb_cl_intersections_list do
            partition_ceiling := ShallowCopy(zeroes);
            partition_ceiling{partition_positions[i]} := List(ceiling{partition_positions[i]} / comb_moduli[i], x -> Int(x)); #Normalizes ceiling by modulus. For any combined class of different modulus, set ceiling to 0. We will generate no new intersections in these positions.

            updated_partial_comb_cl_intersections := PlaceStack(ShallowCopy(partial_comb_cl_intersections), partition_ceiling, 1, partition_stack_sizes[i], partition_stack_sizes[i] + 1); #Build initial updated_partial_comb_cl_intersections
            Append(updated_partial_comb_cl_intersections_list, [ShallowCopy(updated_partial_comb_cl_intersections)]);

            while not NextClassIntersection(updated_partial_comb_cl_intersections, partition_ceiling, partition_stack_sizes[i], comb_cl_intersections_length) = "Done" do #Iterate through updated_partial_comb_cl_intersections
                Append(updated_partial_comb_cl_intersections_list, [ShallowCopy(updated_partial_comb_cl_intersections)]);

                if Length(updated_partial_comb_cl_intersections_list) > 5000000 then
                    return "Space Limits Exceeded";
                fi;
            od;
        od;

        partial_comb_cl_intersections_list := updated_partial_comb_cl_intersections_list; #Reset partial_comb_cl_intersections_list to new updated_partial_comb_cl_intersections_list
    od;

    return partial_comb_cl_intersections_list; #Return another partial list of comb_cl_intersections.
end;

##############################################################################################################
####FILTRATION################################################################################################
#This section is dedicated to efficiently filtering comb_cl_intersections_list, to select only those comb_cl_intersections
#which represent feasible class intersections with a possible PDS.


#We explain the purpose of FiltrationMatrix. Each comb_cl_intersections is generated such that
#       Sum(comb_cl_intersections{partition_positions[i]}) = partition_stack_sizes[i]/comb_moduli[i].
#Therefore, if we define a new vector x such that x{partition_positions[i]} = comb_cl_intersections * comb_moduli[i], then
#x + prelim_cl_intersections represents a full class intersection vector, with the inverse classes combined, so we expect
#       comb_char_mat[i] * x + comb_char_mat[i] * prelim_cl_intersections
#to be a sum of eigenvalues, if x + prelim_cl_intersections represents a valid class intersection for the PDS.

#In practice, it is more computationally expensive to first compute x for each comb_cl_intersections, and then to check that 
#comb_char_mat[i] * x + comb_char_mat[i] * prelim_cl_intersections is a sum of eigenvalues. Instead, we define a new matrix
#filration_mat such that filtration_mat * comb_cl_intersections = comb_char_mat * x. Now, we only need to perform one
#multiplication, which is
#       filtration_mat[i] * comb_cl_intersections + comb_char_mat[i] * prelim_cl_intersections.

FiltrationMatrix := function(comb_char_mat, comb_moduli, v)
    local filtration_mat, i;

    for i in [1..Length(comb_moduli)] do
        if comb_moduli[i] >= v then
            comb_moduli[i] := 1;
        fi;
    od;

    filtration_mat := TransposedMat(comb_char_mat);
    filtration_mat := List([1..Length(comb_moduli)], i -> comb_moduli[i] * filtration_mat[i]);
    filtration_mat := TransposedMat(filtration_mat);

    return filtration_mat;
end;


#Here, we verify that a given comb_cl_intersections is valid. For every combined character degree in comb_char_mat,
#we generate all possible eigenvalue sums.
#Then, for each row i of comb_char_mat and each degree degs[i] in the ith row of comb_char_mat, we compute
#       eigenvalue_sum - comb_char_mat[i] * prelim_cl_intersections
#where eigenvalue_sum is one of the permissible eigenvalue summations generated for the degree degs[i].

#Finally, we check for a given comb_cl_intersections that there is some eigenvalue_sum such that
#               filtration_mat[i] * comb_cl_intersections = eigenvalue_sum - comb_char_mat[i] * prelim_cl_intersections
#given that filtration_mat[i] * comb_cl_intersections + comb_char_mat[i] * prelim_cl_intersections must be an eigenvalue sum
#as previously mentioned.
FilterClassIntersections := function(comb_char_mat, filtration_mat, comb_cl_intersections_list, prelim_cl_intersections, theta1, theta2)
    local 
    deg, degs,
    eigenvalue_degs_list,
    mod_output,
    comb_cl_intersections,
    output_list,
    row,
    i,
    x;

    degs := List(comb_char_mat, row -> row[1]);
    eigenvalue_degs_list := [];

    for deg in Unique(degs) do
        eigenvalue_degs_list[deg] := List([0..deg], x -> theta1*x + theta2*(deg-x));
    od;

    output_list := [];

    for i in [1..Length(comb_char_mat)] do
        mod_output := (comb_char_mat*prelim_cl_intersections)[i];
        output_list[i] := List(eigenvalue_degs_list[degs[i]], x -> x - mod_output);
    od;

    for i in [2..Length(comb_char_mat)] do
        comb_cl_intersections_list := Filtered(comb_cl_intersections_list, comb_cl_intersections -> filtration_mat[i]*comb_cl_intersections in output_list[i]);
    od;

    return comb_cl_intersections_list;
end;

#This is dedicated to verifying that [NS] 4.6 (Thesis 6.6) holds.
FilterInverseClasses := function(cl_intersections_list, index_inv_cls_list, ord_2_cls_list)
    local 
    cl_intersections,
    filtered_cl_intersections_list,
    index_inv_cls,
    keep_intersection,
    i;

    filtered_cl_intersections_list := [];

    for cl_intersections in cl_intersections_list do
        keep_intersection := true;

        for i in [2..Length(index_inv_cls_list)] do
            index_inv_cls := index_inv_cls_list[i];

            if index_inv_cls[1] = index_inv_cls[2] and ord_2_cls_list[i] = false then
                if cl_intersections[index_inv_cls[1]] mod 2 <> 0 then
                    keep_intersection := false;
                fi;
            fi;
        od;

        if keep_intersection then
            Append(filtered_cl_intersections_list, [cl_intersections]);
        fi;
    od;

    return filtered_cl_intersections_list;
end;

##############################################################################################################
#####ALL CLASS INTERSECTIONS##################################################################################

AllClassIntersections := function(group_param_rec, prelim_cl_intersections, moduli)
    local
    char_table, char_mat, v, theta1, theta2,
    stack_size,
    ceiling,
    index_inv_cls_list,
    ord_2_cls_list,
    comb_moduli, comb_char_mat, comb_prelim_cl_intersections, comb_ceiling,
    comb_cl_intersections_length,
    comb_cl_intersections, comb_cl_intersections_list,
    cl_intersections_list,
    partial_comb_cl_intersections_list, #This is an incomplete list of comb_cl_intersections.
    partition_positions,
    filtration_mat,
    partition_ceiling,
    partition_sum_ceiling,
    partition_stacks_sizes, partition_stacks_sizes_list,
    x, #dummy_variable
    i, j; #iterator

    char_table := group_param_rec.char_table;
    char_mat := group_param_rec.char_mat;
    v := group_param_rec.v;
    theta1 := group_param_rec.theta1;
    theta2 := group_param_rec.theta2;

    stack_size := (group_param_rec.k-Sum(prelim_cl_intersections)); #This is the size of the "stack" of elements we need to add to prelim_cl_intersections to reach a valid PDS
    ceiling := List(ConjugacyClasses(char_table), Size) - prelim_cl_intersections; #For each class, ceiling represents the maximum possible number of additional elements we may add

    if Size(Filtered(ceiling, i -> SignInt(i) = -1)) > 0 then #send back the case when stack_size is larger than available space in conjugacy classes
        return [];
    fi;


    x := CombineInverseClasses(char_table, prelim_cl_intersections, ceiling, moduli, char_mat); #We combine inverse classes into one combined class. See CombineInverseClasses for more info.
    index_inv_cls_list := x.index_inv_cls_list;
    comb_prelim_cl_intersections := x.comb_prelim_cl_intersections;
    comb_char_mat := x.comb_char_mat;
    comb_ceiling := x.comb_ceiling; 
    ord_2_cls_list := x.ord_2_cls_list;
    comb_moduli := SelfInverseCombModuli(comb_prelim_cl_intersections, x.comb_moduli, index_inv_cls_list, ord_2_cls_list, v);


    partition_positions := ModuliClassPartition(comb_moduli); #positions of comb_moduli with identical modulus value. See ModuliClassPartition for explanation.
    partition_ceiling := List([1..Length(comb_ceiling)], i -> comb_moduli[i] * Int(comb_ceiling[i]/comb_moduli[i])); #partition_ceiling[i] gives max number of elements which we may add to comb_prelim_cl_intersections[i]
    partition_sum_ceiling := List(partition_positions, x -> Sum(partition_ceiling{x})); #Max number of permissible elements in a given partition

    if Sum(partition_sum_ceiling) < stack_size then
        return [];
    fi;


    partition_stacks_sizes_list := PartitionStackSizes(partition_positions, comb_moduli, partition_sum_ceiling, stack_size); #See PartitionStackSizes for more info.
    comb_cl_intersections_length := Length(comb_moduli)-1; #We subtract one for computational reasons
    filtration_mat := FiltrationMatrix(comb_char_mat, comb_moduli, v); #See FiltrationMatrix for explanation
    comb_cl_intersections_list := [];
    
    for partition_stacks_sizes in partition_stacks_sizes_list do #Iterate over partition_stack_sizes and build all comb_cl_intersections for each partition_stack_sizes
        partial_comb_cl_intersections_list := PartitionClassIntersectionsList(partition_positions, partition_stacks_sizes, comb_moduli, comb_ceiling, comb_cl_intersections_length);

        if partial_comb_cl_intersections_list = "Space Limits Exceeded" then
            return "Space Limits Exceeded";
        fi;

        partial_comb_cl_intersections_list := FilterClassIntersections(comb_char_mat, filtration_mat, partial_comb_cl_intersections_list, comb_prelim_cl_intersections, theta1, theta2);
        Append(comb_cl_intersections_list, partial_comb_cl_intersections_list);
    od;

    for i in [1..Length(comb_cl_intersections_list)] do
        for j in [1..comb_cl_intersections_length+1] do
            comb_cl_intersections_list[i][j] := comb_cl_intersections_list[i][j] * comb_moduli[j];
        od;

        comb_cl_intersections_list[i] := comb_cl_intersections_list[i] + comb_prelim_cl_intersections;
    od;

    cl_intersections_list := UncombineInverseClasses(comb_cl_intersections_list, index_inv_cls_list);
    cl_intersections_list := FilterInverseClasses(cl_intersections_list, index_inv_cls_list, ord_2_cls_list);


    return cl_intersections_list;
end;