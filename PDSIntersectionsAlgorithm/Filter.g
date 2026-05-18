
FilterMinimalIntersection := function(pds_data, min)
	local  phi_1, sum_cl_ints, row;

	phi_1 := pds_data.char_mat * min.cl_ints;
	phi_1 := phi_1 * List(pds_data.char_mat, row -> row[1]); #This corresponds to calculating Phi(1).

	sum_cl_ints := Sum(min.cl_ints);

	if sum_cl_ints > pds_data.k then
		return false;

	elif (sum_cl_ints - pds_data.k) mod pds_data.cp_delta <> 0 then
		return false;

	elif phi_1 mod pds_data.cp_delta <> 0 then
		return false;
	fi;

	return true;
end;


####################################################################################################################


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
