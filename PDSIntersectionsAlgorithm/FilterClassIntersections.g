
##############################################################################################################
####FILTRATION################################################################################################
#We explain the purpose of FiltrationMatrix. Each cmb_cl_ints is generated such that
#	   Sum(cmb_cl_ints{partn_posns[i]}) = partn_stack_sizes[i]/cmb_moduli[i].
#Therefore, if we define a new vector x such that x{partn_posns[i]} = cmb_cl_ints * cmb_moduli[i], then
#x + min_cl_ints represents a full class int vector, with the inverse classes combined, so we expect
#	   cmb_char_mat[i] * x + cmb_char_mat[i] * min_cl_ints
#to be a sum of eigenvalues, if x + min_cl_ints represents a valid class int for the PDS.

#In practice, it is more computationally expensive to first compute x for each cmb_cl_ints, and then to check that 
#cmb_char_mat[i] * x + cmb_char_mat[i] * min_cl_ints is a sum of eigenvalues. Instead, we define a new matrix
#filration_mat such that fltr_mat * cmb_cl_ints = cmb_char_mat * x. Now, we only need to perform one
#multiplication, which is
#	   fltr_mat[i] * cmb_cl_ints + cmb_char_mat[i] * min_cl_ints.

FiltrationMatrix := function(cmb_char_mat, cmb_moduli, v)
	local fltr_mat, i;

	for i in [1..Length(cmb_moduli)] do
		if cmb_moduli[i] >= v then
			cmb_moduli[i] := 1;
		fi;
	od;

	fltr_mat := TransposedMat(cmb_char_mat);
	fltr_mat := List([1..Length(cmb_moduli)], i -> cmb_moduli[i] * fltr_mat[i]);
	fltr_mat := TransposedMat(fltr_mat);

	return fltr_mat;
end;


#Here, we verify that a given cmb_cl_ints is valid. For every combined character degree in cmb_char_mat,
#we generate all possible eigenvalue sums.
#Then, for each row i of cmb_char_mat and each degree degs[i] in the ith row of cmb_char_mat, we compute
#	   eigenvalue_sum - cmb_char_mat[i] * min_cl_ints
#where eigenvalue_sum is one of the permissible eigenvalue summations generated for the degree degs[i].

#Finally, we check for a given cmb_cl_ints that there is some eigenvalue_sum such that
#			   fltr_mat[i] * cmb_cl_ints = eigenvalue_sum - cmb_char_mat[i] * min_cl_ints
#given that fltr_mat[i] * cmb_cl_ints + cmb_char_mat[i] * min_cl_ints must be an eigenvalue sum
#as previously mentioned.
FilterClassIntersections := function(cmb_char_mat, fltr_mat, cmb_cl_ints_lst, min_cl_ints, theta1, theta2)
	local 
	deg, degs,
	eigenvalue_degs_lst,
	mod_output,
	cmb_cl_ints,
	output_lst,
	row,
	i,
	x;

	degs := List(cmb_char_mat, row -> row[1]);
	eigenvalue_degs_lst := [];

	for deg in Unique(degs) do
		eigenvalue_degs_lst[deg] := List([0..deg], x -> theta1*x + theta2*(deg-x));
	od;

	output_lst := [];

	for i in [1..Length(cmb_char_mat)] do
		mod_output := (cmb_char_mat*min_cl_ints)[i];
		output_lst[i] := List(eigenvalue_degs_lst[degs[i]], x -> x - mod_output);
	od;

	for i in [2..Length(cmb_char_mat)] do
		cmb_cl_ints_lst := Filtered(cmb_cl_ints_lst, cmb_cl_ints -> fltr_mat[i]*cmb_cl_ints in output_lst[i]);
	od;

	return cmb_cl_ints_lst;
end;

#This is dedicated to verifying that [NS] 4.6 (Thesis 6.6) holds.
FilterInverseClasses := function(cl_ints_lst, idx_inv_cls_lst, ord_2_cls_lst)
	local 
	cl_ints,
	fltrd_cl_ints_lst,
	idx_inv_cls,
	keep_int,
	i;

	fltrd_cl_ints_lst := [];

	for cl_ints in cl_ints_lst do
		keep_int := true;

		for i in [2..Length(idx_inv_cls_lst)] do
			idx_inv_cls := idx_inv_cls_lst[i];

			if idx_inv_cls[1] = idx_inv_cls[2] and ord_2_cls_lst[i] = false then
				if cl_ints[idx_inv_cls[1]] mod 2 <> 0 then
					keep_int := false;
				fi;
			fi;
		od;

		if keep_int then
			Append(fltrd_cl_ints_lst, [cl_ints]);
		fi;
	od;

	return fltrd_cl_ints_lst;
end;

CoprimeChars := function(irr, sqrt_delta)
	local lin_char_lst, cp_lin_char_lst;

	lin_char_lst := Filtered( irr, char -> char[1] = 1);
	cp_lin_char_lst := Filtered(lin_char_lst, char -> Gcd(sqrt_delta, Order(char)) = 1);

	return cp_lin_char_lst;
end;

VerifyCosetIntersections := function(cl_ints, group, irr, cls, v, k, sqrt_delta)
	local
	theta_alpha,
	cp_ln_char_lst, char,
	N,
	cosets, coset_size, cl,
	cl_coset_subset_lst, subset_cls,
	i;

	cp_ln_char_lst := CoprimeChars(irr, sqrt_delta);

	if Length(cp_ln_char_lst) = 1 then
		return true;
	fi;
	
	theta_alpha := cl_ints * AsList(cp_ln_char_lst[2]);


	N := Intersection( List(cp_ln_char_lst, char -> KernelOfCharacter(char)));
	cosets := RightCosets(group, N);

	cl_coset_subset_lst := [];

	for i in [1..Length(cosets)] do
		subset_cls := Filtered(cls, cl -> IsSubset(cosets[i], cl));
		cl_coset_subset_lst[i] := List(subset_cls, cl -> Position(cls, cl));
	od;

	coset_size := (k - theta_alpha) * (Size(N)/v);

	if not IsInt(coset_size) then
		return false;
	fi;

	for i in [2..Length(cosets)] do
		if Sum(cl_ints{cl_coset_subset_lst[i]}) > coset_size then
			return false;
		fi;
	od;

	return true;
end;

FilterCosetIntersections := function(cl_ints_lst, group, irr, cls, v, k, sqrt_delta)
	return Filtered(cl_ints_lst, cl_ints -> VerifyCosetIntersections(cl_ints, group, irr, cls, v, k, sqrt_delta));
end;

