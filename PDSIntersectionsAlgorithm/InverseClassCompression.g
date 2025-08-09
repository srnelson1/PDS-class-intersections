
##############################################################################################################
####INVERSE CLASS COMPRESSION#################################################################################
#Following from the fact that D^(-1) = D, we get |h^G \cap D| = | (h^-1)^G \cap D|. Thus, when we generate a class int,
#this class int must satisfy |h^G \cap D| = | (h^-1)^G \cap D| for all h^G. So, we instead compute our ints by
#cmbining |(h^G \cup (h^G)^{-1]) \cap D|. If c, c' are the moduli corresponding h^G, (h^G)^{-1}, we set our new modulus
#for |(h^G \cup (h^G)^{-1]) \cap D| to c + c'. In practice, this means we have fewer ints to search through with larger
#moduli, speeding up search times.

#For class representatives h_1, ..., h_n, return lst of pairs [i, j] such that h_i^G = (h_j^G)^{-1}
IndexInverseClassList := function(reps, cls)
	local idx_inv_cls_lst, cl, inv_cl, x, i;

	idx_inv_cls_lst := [];

	for i in [1..Length(cls)] do
		cl := cls[i];

		inv_cl := Filtered(cls, x -> Inverse( reps[i] ) in x)[1];
		
		Append(idx_inv_cls_lst, [ [Position(cls, inv_cl), Position(cls, cl)] ]);
		Sort( Last(idx_inv_cls_lst) );
	od;

	idx_inv_cls_lst := Unique(idx_inv_cls_lst);
	Sort(idx_inv_cls_lst);

	return idx_inv_cls_lst;
end;

#For min_cl_ints, ceiling, etc., we build new lsts cmb_min_cl_ints, cmb_ceiling, etc.
#which correspond to the combined ints |(h^G \cup (h^G)^{-1]) \cap D|.


#For those classes h^G satisfying h^G = h^{-1}^G but h <> h^{-1}, for which their modulus is odd, we enforce the modulus is even.
#See LEMMA from PAPER
SelfInverseCombModuli := function(cmb_min_cl_ints, cmb_moduli, idx_inv_cls_lst, ord_2_cls_lst, v)
	local i;

	for i in [1..Length(idx_inv_cls_lst)] do
		if (idx_inv_cls_lst[i][1] = idx_inv_cls_lst[i][2]) and (ord_2_cls_lst[i] = false) then
			if cmb_min_cl_ints[i] mod 2 = 0 and cmb_moduli[i] mod 2 = 1 then 
				cmb_moduli[i] := 2*cmb_moduli[i];
			fi;
		fi;
	od;

	return cmb_moduli;
end;

CombineInverseClasses := function(pds_data, ceiling, min_cl_ints, moduli)
    local
    char_table, char_mat,
    cl, cls, ord_2_cls_lst, reps,
    idx_inv_cls_lst, #lst of elements [i, j] such that i is the idx of the ith conjugacy class and j the idx of its inverse
    cmb_min_cl_ints, #new min_cl_ints such that idx i 
    cmb_ceiling,
    cmb_char_mat,
    cmb_moduli,
    x,
    i;

    char_table := pds_data.char_table;
    char_mat := pds_data.char_mat;
    cls := pds_data.cls;

    reps := List(cls, cl -> Representative(cl));
    ord_2_cls_lst := List(reps, x -> Order(x) = 2);
    idx_inv_cls_lst := IndexInverseClassList(reps, cls);


    cmb_min_cl_ints := [];
    cmb_ceiling := [];
    cmb_moduli := [];
    cmb_char_mat := [];


    char_mat := TransposedMat(char_mat);
    

    for i in [1..Length(idx_inv_cls_lst)] do
        if idx_inv_cls_lst[i][1] <> idx_inv_cls_lst[i][2] then
            cmb_min_cl_ints[i] := min_cl_ints[idx_inv_cls_lst[i][1]] + min_cl_ints[idx_inv_cls_lst[i][2]];
            cmb_ceiling[i] := ceiling[idx_inv_cls_lst[i][1]] + ceiling[idx_inv_cls_lst[i][2]];
            cmb_moduli[i] := moduli[idx_inv_cls_lst[i][1]] + moduli[idx_inv_cls_lst[i][2]];
            cmb_char_mat[i] := (char_mat[idx_inv_cls_lst[i][1]] + char_mat[idx_inv_cls_lst[i][2]])/2; #Say idx_inv_cls_lst[k] = [i, j], then when we generate cmb_cl_intersection, we want cmb_char_mat[k] * cmb_cl_intersection = char_mat[i] * cl_intersection + char_mat[j] * cl_intersection. This requires division by 2.
        else
            cmb_min_cl_ints[i] := min_cl_ints[idx_inv_cls_lst[i][1]];
            cmb_ceiling[i] := ceiling[idx_inv_cls_lst[i][1]];
            cmb_moduli[i] := moduli[idx_inv_cls_lst[i][1]];
            cmb_char_mat[i] := char_mat[idx_inv_cls_lst[i][1]];
        fi;
    od;

    cmb_char_mat := TransposedMat(cmb_char_mat);
    cmb_moduli := SelfInverseCombModuli(cmb_min_cl_ints, cmb_moduli, idx_inv_cls_lst, ord_2_cls_lst, pds_data.v);

    return  rec(
		min_cl_ints := cmb_min_cl_ints,
		idx_inv_cls_lst := idx_inv_cls_lst,
		ceiling := cmb_ceiling,
		moduli := cmb_moduli,
		char_mat := cmb_char_mat,
		len := Length(cmb_ceiling),
		ord_2_cls_lst := ord_2_cls_lst
        );
end;

#We uncmbine all cmb_cl_ints in cl_ints_lst.
UncombineInverseClasses := function(cl_ints_lst, idx_inv_cls_lst)
	local
	cl_ints,
	cmb_cl_ints,
	num_cls,
	idx_inv_cls,
	i, j;

	num_cls := Length(Flat(idx_inv_cls_lst));

	for i in [1..Length(cl_ints_lst)] do
		cmb_cl_ints := cl_ints_lst[i];
		cl_ints := EmptyPlist(num_cls);

		for j in [1..Length(idx_inv_cls_lst)] do
			idx_inv_cls := idx_inv_cls_lst[j];
			
			if idx_inv_cls[1] <> idx_inv_cls[2] then
				cl_ints[idx_inv_cls[1]] := cmb_cl_ints[j]/2;
				cl_ints[idx_inv_cls[2]] := cmb_cl_ints[j]/2;
			else
				cl_ints[idx_inv_cls[1]] := cmb_cl_ints[j];
			fi;
		od;

		cl_ints_lst[i] := cl_ints;
	od;

	return cl_ints_lst;
end;

