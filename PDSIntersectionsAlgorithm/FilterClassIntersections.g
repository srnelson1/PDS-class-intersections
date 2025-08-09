

FiltrationMatrix := function(cmb, v)
	local fltr_mat, i;

	for i in [1..Length(cmb.moduli)] do
		if cmb.moduli[i] >= v then
			cmb.moduli[i] := 1;
		fi;
	od;

	fltr_mat := TransposedMat(cmb.char_mat);
	fltr_mat := List([1..Length(cmb.moduli)], i -> cmb.moduli[i] * fltr_mat[i]);
	fltr_mat := TransposedMat(fltr_mat);

	return fltr_mat;
end;


FiltrationList := function(pds_data, cmb_char_mat, min_cl_ints)
	local
	degs, deg,
	evalue_degs_lst,
	fltr_lst,
	mod_output,
	i,
	x;

	degs := List(cmb_char_mat, row -> row[1]);
	evalue_degs_lst := [];

	for deg in Unique(degs) do
		evalue_degs_lst[deg] := List([0..deg], x -> pds_data.theta1 * x + pds_data.theta2 * (deg-x));
	od;

	fltr_lst := [];

	for i in [1..Length(cmb_char_mat)] do
		mod_output := (cmb_char_mat * min_cl_ints)[i];
		fltr_lst[i] := List(evalue_degs_lst[degs[i]], x -> x - mod_output);
	od;

	return fltr_lst;
end;


Filtration := function(pds_data, cmb, min_cl_ints)
	local fltr_lst, fltr_mat;

	fltr_mat := FiltrationMatrix(cmb, pds_data.v);
	fltr_lst := FiltrationList(pds_data, cmb.char_mat, min_cl_ints);

	return rec(
		fltr_mat := fltr_mat,
		fltr_lst := fltr_lst
	);
end;


####################################################################################################################


FilterOutput := function(fltr_mat, fltr_lst, cl_ints)
	local i;

	for i in [2..Length(fltr_mat)] do
		if not fltr_mat[i] * cl_ints in fltr_lst[i] then 
			return false;
		fi;
	od;

	return true;
end;


FilterInverseClasses := function(cl_ints, idx_inv_cls_lst, ord_2_cls_lst)
	local 
	fltrd_cl_ints_lst,
	idx_inv_cls,
	keep_int,
	i;

	for i in [2..Length(idx_inv_cls_lst)] do
		idx_inv_cls := idx_inv_cls_lst[i];

		if idx_inv_cls[1] = idx_inv_cls[2] and ord_2_cls_lst[i] = false then
			if cl_ints[idx_inv_cls[1]] mod 2 <> 0 then
				return false;
			fi;
		fi;
	od;

	return true;
end;


ValidClassIntersection := function(fltr, cmb, cl_ints)

	if not FilterOutput(fltr.fltr_mat, fltr.fltr_lst, cl_ints) then
		return false;
	fi;

#	if not FilterInverseClasses(cl_ints, cmb.idx_inv_cls_lst, cmb.ord_2_cls_lst) then
#		return false;
#	fi;

	return true;
end;
