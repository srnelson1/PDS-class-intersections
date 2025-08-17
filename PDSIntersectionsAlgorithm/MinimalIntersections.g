
####################################################################################################################

ClassesOutsideN := function(pds_data)
	local
	lin_chars, cp_lin_chars, lin_char, order,
	cl, extN_cls,
	ones,
	idx,
	x;

	lin_chars := Filtered(pds_data.char_mat, x -> x[1] = 1);

	cp_lin_chars := [];
	extN_cls := [];

	for lin_char in lin_chars do
		order := Maximum( List(lin_char, x -> Conductor(x)) );

		if Gcd(order, pds_data.theta1 - pds_data.theta2) = 1 then
			Append(cp_lin_chars, [lin_char]);
		fi;
	od;

	ones := ListWithIdenticalEntries(Length(cp_lin_chars), 1);

	for cl in pds_data.cls do
		idx := Position(pds_data.cls, cl);

		if List(cp_lin_chars, x -> x[idx]) <> ones then
			Append(extN_cls, [cl]);
		fi;
	od;
	
	return extN_cls;
end;


ValidTheta := function(pds_data, extN_cls)
	local
	zeroes,
	centralizer_sizes,
	cl,
	evalues,
	valid_theta;

	zeroes := ListWithIdenticalEntries(Length(extN_cls), 0);

	centralizer_sizes := List(extN_cls, cl -> Int( pds_data.v / Size(cl) ) );
	evalues := [pds_data.theta1, pds_data.theta2];

	valid_theta := Filtered(evalues, x -> (pds_data.k - x) mod centralizer_sizes = zeroes);

	return valid_theta;
end;


ExtNClIntersections := function(pds_data)
	local
	extN_cls, extN_cls_idx,
	valid_theta, theta, theta_ints, theta_lst,
	i;

	extN_cls := ClassesOutsideN(pds_data);
	extN_cls_idx := List(extN_cls, cl -> Position(pds_data.cls, cl));

	valid_theta := ValidTheta(pds_data, extN_cls);
	theta_ints := [];

	for theta in valid_theta do
		theta_lst := EmptyPlist(Length(pds_data.cls));

		for i in extN_cls_idx do
			theta_lst[i] := pds_data.k - theta;
			theta_lst[i] := theta_lst[i] / (pds_data.v / Size( pds_data.cls[i] ));
			theta_lst[i] := Int(theta_lst[i]);
		od;

		Append(theta_ints, [theta_lst]);
	od;

	theta_ints := Unique(theta_ints);

	return theta_ints;
end;

####################################################################################################################

ModularIntersections := function(centralizer_sizes,  k, theta2, q)
	local 
	cl_mod_q_ints, #class ints mod q
	i; #iteration

	cl_mod_q_ints := EmptyPlist(Length(centralizer_sizes));

	for i in [1..Length(centralizer_sizes)] do
		if centralizer_sizes[i] mod q <> 0 then #i for which  (k-theta2)/centralizer_sizes[i] is computable mod q (these correspond to p_bound_values)
			cl_mod_q_ints[i] := (k-theta2)/centralizer_sizes[i] mod q; #compute int mod q.
		fi;
	od;

	return cl_mod_q_ints;
end;


QModularClassRecord := function(pds_data, prime_powers_delta, num_cls)
	local
	centralizer_sizes,
	cl_mod_q_ints_rec,
	q;


	centralizer_sizes := List(pds_data.cls, cl -> Int( pds_data.v / Size(cl) ) );

	cl_mod_q_ints_rec := rec( 1 := ListWithIdenticalEntries(num_cls, 0));

	for q in prime_powers_delta do
		if q <> 1 then
			cl_mod_q_ints_rec.(q) := ModularIntersections(centralizer_sizes, pds_data.k, pds_data.theta1, q);
		fi;
	od;

	return cl_mod_q_ints_rec;
end;


ModularValues := function(pds_data, cl_mod_q_ints_rec, prime_powers_delta, num_cls)
	local
	cl_ints, vals,
	defined_q_values, defined_cl_q_ints,
	q,
	i;

	cl_ints := EmptyPlist(num_cls); #will contain largest possible minimum int size for each conjugacy class using Chinese Remainder Theorem
	vals := EmptyPlist(num_cls); #contains Chinese Remainder Theorem value for which the ith int is valid.

	for i in [2..num_cls] do
		defined_q_values := Filtered(prime_powers_delta, q -> IsBound( cl_mod_q_ints_rec.(q)[i]) ); 
		defined_cl_q_ints := List(defined_q_values, q -> cl_mod_q_ints_rec.(q)[i] ); 

		cl_ints[i] := ChineseRem(defined_q_values, defined_cl_q_ints);
		vals[i] := Product(defined_q_values);
	od;

	cl_ints[1] := (pds_data.k - pds_data.theta2 + pds_data.v*pds_data.theta2) mod pds_data.cp_delta;
	vals[1] := pds_data.k;

	return rec(
			cl_ints := cl_ints,
			vals := vals
		);
end;


ModularClassIntersections := function(pds_data)
	local 
	num_cls,
	primes_delta, prime_powers_delta,
	cl_mod_q_ints_rec,
	modular;


	num_cls := Length(pds_data.cls);

	primes_delta := PrimePowersInt(pds_data.theta1-pds_data.theta2);
	prime_powers_delta := List([1.. Length(primes_delta)/2], i -> primes_delta[2*i - 1] ^ primes_delta[2*i]);
	Append(prime_powers_delta, [1]);

	cl_mod_q_ints_rec := QModularClassRecord(pds_data, prime_powers_delta, num_cls);

	modular := ModularValues(pds_data, cl_mod_q_ints_rec, prime_powers_delta, num_cls);

	return modular;
end;

####################################################################################################################

IsValidMinimalIntersection := function(pds_data, min)
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

MinimalIntersectionsList := function(pds_data, modular, extN_ints_lst)
	local
	extN_ints,
	min_lst, min,
	i;

	min_lst := [];

	for extN_ints in extN_ints_lst do
		min := rec( cl_ints := extN_ints, moduli := ShallowCopy(modular.vals) );

		for i in [1.. Length(pds_data.cls)] do
			if IsBound(extN_ints[i]) then
				min.moduli[i] := pds_data.k;
			else
				min.cl_ints[i] := modular.cl_ints[i];
			fi;
		od;

		Append(min_lst, [min]);
	od;

	return min_lst;
end;


MinimalIntersections := function(pds_data)
	local
	modular,
	extN_ints_lst,
	min, min_lst,
	i;

	modular := ModularClassIntersections(pds_data);
	#TODO: ADD EVEN ORDER MODULUS CHECKING
	extN_ints_lst := ExtNClIntersections(pds_data);

	min_lst := MinimalIntersectionsList(pds_data, modular, extN_ints_lst);
	min_lst := Filtered(min_lst, min -> IsValidMinimalIntersection(pds_data, min) );
	
	return min_lst;
end;
