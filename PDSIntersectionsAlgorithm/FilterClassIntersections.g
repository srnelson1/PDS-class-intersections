

FiltrationMatrix := function(pds_data, cmb)
	local mat, i;

	for i in [1..Length(cmb.moduli)] do
		if cmb.moduli[i] >= pds_data.v then
			cmb.moduli[i] := 1;
		fi;
	od;

	mat := TransposedMat(cmb.char_mat);
	mat := List([1..Length(cmb.moduli)], i -> cmb.moduli[i] * mat[i]);
	mat := TransposedMat(mat);

	return mat;
end;


FiltrationList := function(pds_data, cmb)
	local 
	deg, degs,
	chi_D_lst,
	lst,
	x,
	i;

	degs := List(cmb.char_mat, x -> x[1]);
	chi_D_lst := [];

	for deg in Unique(degs) do
	    chi_D_lst[deg] := List([0..deg], x -> pds_data.theta1*x + pds_data.theta2*(deg-x));
	od;

	lst := [];

	for i in [1..Length(cmb.char_mat)] do
	    lst[i] := List(chi_D_lst[degs[i]], x -> x - (cmb.char_mat * cmb.min_cl_ints)[i]);
	od;

	return lst;
end;


Filtration := function(pds_data, cmb)
	return rec(
		mat := FiltrationMatrix(pds_data, cmb),
		lst := FiltrationList(pds_data, cmb)
	);
end;


####################################################################################################################


FilterOutput := function(fltr, cl_ints)
	local i;

	for i in [2..Length(fltr.mat)] do
		if not fltr.mat[i] * cl_ints in fltr.lst[i] then 
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

	if not FilterOutput(fltr, cl_ints) then
		return false;
	fi;

#	if not FilterInverseClasses(cl_ints, cmb.idx_inv_cls_lst, cmb.ord_2_cls_lst) then
#		return false;
#	fi;

	return true;
end;
