
#Testing Swartz-Tauschek modularity restrictions.
STRestriction := function(group, v, k, lambda, mu)
	local sqrtDelta, theta1, theta2, gamtest, gamcomptest;

	sqrtDelta:= RootInt( (lambda - mu)^2 + 4*(k - mu) );
	theta1:= (lambda - mu + sqrtDelta)/2;
	theta2:= (lambda - mu - sqrtDelta)/2;



	if RemInt(mu - theta2*(theta1 + 1), sqrtDelta) = 0 then
		gamtest:= true;
	else
		gamtest:= false;
	fi;

	#Apply the test to the complement.

	if RemInt(v - 2*k + lambda - theta2*(theta1 + 1), sqrtDelta) = 0 then
		gamcomptest:= true;
	else
		gamcomptest:= false;
	fi;		

	#Return the results. Which graph "failed" the test (and would thus
	#need to have every conjugacy class meet the PDS) is lsted in parentheses.

	if ( not gamtest ) and ( not gamcomptest ) then
		if Size( Center(group) ) <> 1 then
			return false;
		fi;
	fi;

	return true;
end;

