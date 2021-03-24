(* ::Package:: *)

(* ::Section:: *)
(*represenatations*)


matO2=({
 {0, -1, 1},
 {1, 1, 0},
 {1, -1, -2}
});
signO2={-1,-1,+1};
matSU4=({
 {0, -1, 1},
 {1, 1, 2/3},
 {1, -1, -4/3}
});
signSU4={+1,+1,-1};


matO2SU4=KroneckerProduct[matO2,matSU4];
signO2SU4=KroneckerProduct[signO2,signSU4]//Flatten;


reps=Flatten[Outer[
	{#1[[1]],#2[[1]],Switch[#1[[2]]*#2[[2]],1,EvenQ,-1,OddQ]}&,
	{{so2[S],1},{so2[A],-1},{so2[T],1}},
	{{su4[0],1},{su4[1],-1},{su4[2],1}},1
],1]


repsIdx=<||>;
Do[
	repsIdx[reps[[idx,;;2]]]=idx,
	{idx,Length[reps]}
] 


(* ::Section:: *)
(*Compute functionals*)


(* ::Subsection:: *)
(*read polynomials from ScalarBlock output*)


(*ClearAll[getDBlockDictionary]
getDBlockDictionary[fdr_]:=Block[
	{name,spin},
	Map[
		(
			name=#;
			spin=ToExpression[StringSplit[StringSplit[#,"L"][[2]],"-"][[1]]];
			spin->Association[ Get[name] ]
		)&,
		FileNames[fdr<>"/*.m"]
	]
]//Association*)


getPoles[dBlockDictionary_]:=(#[shiftedPoles])&/@dBlockDictionary//KeySort


(* ::Subsection:: *)
(*channel dictionary*)


generateChannelDictionary[Lambda_,dBlockDictionary_]:=Block[
	{
		d=3,\[Delta]gaps=0,
		mat=KroneckerProduct[matO2,matSU4],
		sign=KroneckerProduct[signO2,signSU4]//Flatten,
		polynomials,
		spins,chn,shift0,shift,
		bulk,isolated,pols,vac,polesArray,poleZeroCanceled,
		gaps,\[CapitalDelta]M1,(*\[CapitalDelta]MHalf=psuNL5Run1[[-1]]["\[CapitalDelta]MHalf"],*)
		out,chnToIdx
	},
	spins=dBlockDictionary//Keys;
	bulk=Flatten[Table[
		chn=reps[[idxChn]];
		Table[
			<|
				"channel"->chn[[;;2]],
				"spin"->l
			|>,
			{l,Select[spins,reps[[idxChn,3]]]}
		],
		{idxChn,9}
	],1];
	chnToIdx=<||>;
	MapIndexed[
		(chnToIdx[#1]=#2[[1]])&,
		{#channel,#spin}&/@bulk
	];
	chnToIdx
]


(* ::Subsection:: *)
(*Take derivatives of dBlock polynomials symbolically*)


computeDBlockPolyAndDeriv[dBlockDictionary_]:=Block[
	{p,pd,pdd},
	Association/@Association[Reap[Do[
		p = dBlockDictionary[l,key];
		pd = D[p,\[CapitalDelta]];
		pdd = D[pd,\[CapitalDelta]];
		Sow[Flatten[{List@@key,0}]->p,l];
		Sow[Flatten[{List@@key,1}]->pd,l];
		Sow[Flatten[{List@@key,2}]->pdd,l];,
		{l,Keys[dBlockDictionary]},
		{key,Cases[Keys[dBlockDictionary[l]],zzbDeriv[__]]}
	],_,Rule ][[2]] ]
]


(* ::Subsection:: *)
(*compute the derivatives of (1/2)^\[CapitalDelta]Ext Pochhammer[\[CapitalDelta]Ext-m+k+1,m-k] factors*)


(* Note this has 0/0 singularity at \[CapitalDelta]Ext=integers. One should avoid these zeros. *)
computeExtFactorDeriv[Lambda_,\[CapitalDelta]Ext_]:=Block[
	{n},
	Reap[Do[
		n=d-m;
		Do[
			Sow[{m,n,k,kp,0}->(Binomial[m,k]Binomial[n,kp]
				(1/2)^(\[CapitalDelta]Ext-m+k) (1/2)^(\[CapitalDelta]Ext-n+kp)
				Pochhammer[\[CapitalDelta]Ext-m+k+1,m-k]
				Pochhammer[\[CapitalDelta]Ext-n+kp+1,n-kp])];
			Sow[{m,n,k,kp,1}->(-2^(-k-kp+m+n-2 \[CapitalDelta]Ext) *
				Binomial[m,k]Binomial[n,kp]
				Pochhammer[1+k-m+\[CapitalDelta]Ext,-k+m] 
				Pochhammer[1+kp-n+\[CapitalDelta]Ext,-kp+n]
				(Log[4]-2 PolyGamma[0,1+\[CapitalDelta]Ext]+PolyGamma[0,1+k-m+\[CapitalDelta]Ext]+PolyGamma[0,1+kp-n+\[CapitalDelta]Ext]))
			];
			Sow[{m,n,k,kp,2}->(2^(-k-kp+m+n-2 \[CapitalDelta]Ext)  
				Binomial[m,k]Binomial[n,kp]
				Pochhammer[1+k-m+\[CapitalDelta]Ext,-k+m] 
				Pochhammer[1+kp-n+\[CapitalDelta]Ext,-kp+n] 
				(4 Log[2]^2+4 PolyGamma[0,1+\[CapitalDelta]Ext]^2
					+PolyGamma[0,1+k-m+\[CapitalDelta]Ext]^2
					+Log[16] PolyGamma[0,1+kp-n+\[CapitalDelta]Ext]
					+PolyGamma[0,1+kp-n+\[CapitalDelta]Ext]^2
					+2 PolyGamma[0,1+k-m+\[CapitalDelta]Ext] 
					(Log[4]+PolyGamma[0,1+kp-n+\[CapitalDelta]Ext])
					-4 PolyGamma[0,1+\[CapitalDelta]Ext] *
					(Log[4]+PolyGamma[0,1+k-m+\[CapitalDelta]Ext]
						+PolyGamma[0,1+kp-n+\[CapitalDelta]Ext])
					+2 PolyGamma[1,1+\[CapitalDelta]Ext]
					-PolyGamma[1,1+k-m+\[CapitalDelta]Ext]
					-PolyGamma[1,1+kp-n+\[CapitalDelta]Ext])  )
			],
			{k,0,m},{kp,0,n}
		],
		{d,0,Lambda},{m,Range[Ceiling[d/2],d]}
	] ][[2,1]]//Association
]


(* ::Subsection:: *)
(*combine the \[CapitalDelta]Ext factors and the dBlock polynomials*)


(* dBlockPoly will be numerical *)
combineExtFactorAndDeriv[Lambda_,derivsOddOrEvenQ_,extFactors_,dBlockPoly_]:=Block[
	{n},
	Table[
		deriv->Flatten[Table[
			n=d-m;
			Sum[
				extFactors[{m,n,k,kp,deriv[[1]]}]*(-1)^(m-k+n-kp)*
				dBlockPoly[{Max[k,kp],Min[k,kp],deriv[[2]]} ],
				{k,0,m},{kp,0,n}
			],
			{d,Select[Range[0,Lambda],derivsOddOrEvenQ]},
			{m,Range[Ceiling[d/2],d]}
		],1],
	{deriv,{{0,0},{0,1},{0,2},{1,0},{1,1},{2,0},{2,1}}} ]//Association
]


(* ::Subsection:: *)
(*combine the functional polynomials with poles and damping factors*)


ClearAll[evaluateDampedRationals]
evaluateDampedRationals[{P_,Pp_,Ppp_},poles_,r0_,x_]:=Block[
{
	valA,valAp,valApp,valB,valBpOverB,valBpOverBDeriv,
	valF,valFp,valFpp
},
(* function is defined as A[x]/B[x]
where A[x] := p[x]*r0^x,  r0 < 1
p[x], p'[x] and p''[x] are given as numbers,
and B[x] := Product[x-xi,{xi,poles}]
*)
	valA = P*r0^x;
	valAp = Pp*r0^x + P*r0^x*Log[r0];
	valApp = Ppp*r0^x + 2Pp*r0^x*Log[r0] + P*r0^x*Log[r0]^2;
	valB = Product[(x-xi),{xi,poles}];
	valBpOverB = Sum[1/(x-xj),{xj,poles}];
	valBpOverBDeriv = Sum[-1/(x-xj)^2,{xj,poles}];
	
	valF = valA/valB;
	valFp = valAp/valB - valA/valB * valBpOverB;
	valFpp = valApp/valB 
			- 2 * valAp/valB * valBpOverB 
			+ valA(valBpOverB^2/valB - valBpOverBDeriv/valB);
	
	{valF,valFp,valFpp}

]
evaluateDampedRationals[{P_,Pp_},poles_,r0_,x_]:=Block[
{
	valA,valAp,valB,valBpOverB,
	valF,valFp
},
(* This is the same function as above but only compute to 
first derivative *)
	valA = P*r0^x;
	valAp = Pp*r0^x + P*r0^x*Log[r0];
	valB = Product[(x-xi),{xi,poles}];
	valBpOverB = Sum[1/(x-xj),{xj,poles}];
	
	valF = valA/valB;
	valFp = valAp/valB - valA/valB * valBpOverB;
	
	{valF,valFp}

];
evaluateDampedRationals[{P_},poles_,r0_,x_]:=Block[
{
	valA,valAp,valB,valBpOverB,
	valF,valFp
},
(* This is the same function as above but only compute to 
first derivative *)
	valA = P*r0^x;
	valB = Product[(x-xi),{xi,poles}];
	
	valF = valA/valB;
	
	{valF}

]


ClearAll[evaluateRationals]
evaluateRationals[{P_,Pp_,Ppp_},poles_,x_]:=Block[
{
	valA,valAp,valApp,valB,valBpOverB,valBpOverBDeriv,
	valF,valFp,valFpp
},
(* function is defined as A[x]/B[x]
where A[x] := p[x]*r0^x,  r0 < 1
p[x], p'[x] and p''[x] are given as numbers,
and B[x] := Product[x-xi,{xi,poles}]
*)
	valA = P;
	valAp = Pp;
	valApp = Ppp;
	valB = Product[(x-xi),{xi,poles}];
	valBpOverB = Sum[1/(x-xj),{xj,poles}];
	valBpOverBDeriv = Sum[-1/(x-xj)^2,{xj,poles}];
	
	valF = valA/valB;
	valFp = valAp/valB - valA/valB * valBpOverB;
	valFpp = valApp/valB 
			- 2 * valAp/valB * valBpOverB 
			+ valA(valBpOverB^2/valB - valBpOverBDeriv/valB);
	
	{valF,valFp,valFpp}

]
evaluateRationals[{P_,Pp_},poles_,x_]:=Block[
{
	valA,valAp,valB,valBpOverB,
	valF,valFp
},
(* This is the same function as above but only compute to 
first derivative *)
	valA = P;
	valAp = Pp;
	valB = Product[(x-xi),{xi,poles}];
	valBpOverB = Sum[1/(x-xj),{xj,poles}];
	
	valF = valA/valB;
	valFp = valAp/valB - valA/valB * valBpOverB;
	
	{valF,valFp}

];
evaluateRationals[{P_},poles_,x_]:=Block[
{
	valA,valAp,valB,valBpOverB,
	valF,valFp
},
(* This is the same function as above but only compute to 
first derivative *)
	valA = P;
	valB = Product[(x-xi),{xi,poles}];
	
	valF = valA/valB;
	
	{valF}

]


(* ::Subsection:: *)
(*main function - output channels*)


With[{d=3},unitarityGap[l_]:=If[l==0,1/2(d-2),l+d-2] ];


ClearAll[computeBulkChannel]
computeBulkChannel[rep_,spin_,xFromUnitary_,
	Lambda_,polesAssociation_,dBlockPoly_,extFactors_]:=Block[
	{idxChn=repsIdx[rep],l=spin,d=3,
	polynomials,r0=3-2Sqrt[2],
	\[CapitalDelta]0,
	dBlockPolyN,functionalsPoly,dampedRationals},
	
	unitarityGap[l_]:=If[l==0,1/2(d-2),l+d-2];
	\[CapitalDelta]0 = xFromUnitary+unitarityGap[l];
	dBlockPolyN = Map[#/.\[CapitalDelta]->\[CapitalDelta]0&,dBlockPoly[l]];
	polynomials[-1]=combineExtFactorAndDeriv[Lambda,OddQ,extFactors,dBlockPolyN];
	polynomials[1]=combineExtFactorAndDeriv[Lambda,EvenQ,extFactors,dBlockPolyN];
	
	functionalsPoly = Table[
		deriv->Flatten[Table[
			matO2SU4[[idxEqn,idxChn]]*
			polynomials[signO2SU4[[idxEqn]] ][deriv],
		{idxEqn,9}],1],
	{deriv,{{0,0},{0,1},{0,2},{1,0},{1,1},{2,0}}}]//Association;
	
	
	
	dampedRationals = MapThread[Rule,{
		{{0,0},{0,1},{0,2}},
		evaluateDampedRationals[
			{functionalsPoly[{0,0}],
			functionalsPoly[{0,1}],
			functionalsPoly[{0,2}]},
			polesAssociation[l],r0,\[CapitalDelta]0]
	}]~Join~
	MapThread[Rule,{
		{{1,0},{1,1}}, 
		evaluateDampedRationals[
			{functionalsPoly[{1,0}],
			functionalsPoly[{1,1}]},
			polesAssociation[l],r0,\[CapitalDelta]0]
	}]~Join~
	{
		{2,0}->evaluateDampedRationals[
			{functionalsPoly[{2,0}]},
			polesAssociation[l],r0,\[CapitalDelta]0 ][[1]]
	}//Association;
	
	dampedRationals
]


ClearAll[computeBulkChannelNoDamp]
computeBulkChannelNoDamp[rep_,spin_,xFromUnitary_,
	Lambda_,polesAssociation_,dBlockPoly_,extFactors_]:=Block[
	{idxChn=repsIdx[rep],l=spin,d=3,
	polynomials,
	\[CapitalDelta]0,
	dBlockPolyN,functionalsPoly,dampedRationals},
	
	unitarityGap[l_]:=If[l==0,1/2(d-2),l+d-2];
	\[CapitalDelta]0 = xFromUnitary+unitarityGap[l];
	dBlockPolyN = Map[#/.\[CapitalDelta]->\[CapitalDelta]0&,dBlockPoly[l]];
	polynomials[-1]=combineExtFactorAndDeriv[Lambda,OddQ,extFactors,dBlockPolyN];
	polynomials[1]=combineExtFactorAndDeriv[Lambda,EvenQ,extFactors,dBlockPolyN];
	
	functionalsPoly = Table[
		deriv->Flatten[Table[
			matO2SU4[[idxEqn,idxChn]]*
			polynomials[signO2SU4[[idxEqn]] ][deriv],
		{idxEqn,9}],1],
	{deriv,{{0,0},{0,1},{0,2},{1,0},{1,1},{2,0}}}]//Association;
	
	
	
	dampedRationals = MapThread[Rule,{
		{{0,0},{0,1},{0,2}},
		evaluateRationals[
			{functionalsPoly[{0,0}],
			functionalsPoly[{0,1}],
			functionalsPoly[{0,2}]},
			polesAssociation[l],\[CapitalDelta]0]
	}]~Join~
	MapThread[Rule,{
		{{1,0},{1,1}}, 
		evaluateRationals[
			{functionalsPoly[{1,0}],
			functionalsPoly[{1,1}]},
			polesAssociation[l],\[CapitalDelta]0]
	}]~Join~
	{
		{2,0}->evaluateRationals[
			{functionalsPoly[{2,0}]},
			polesAssociation[l],\[CapitalDelta]0 ][[1]]
	}//Association;
	
	dampedRationals
]


ClearAll[computeConservedChannel]
computeConservedChannel[rep_,spin_,
	Lambda_,polesAssociation_,dBlockPoly_,extFactors_]:=Block[
	{idxChn=repsIdx[rep],l=spin,d=3,
	polynomials,\[CapitalDelta]0,
	dBlockPolyN,functionalsPoly,poleZeroCanceled},
	
	\[CapitalDelta]0 = unitarityGap[l];
	dBlockPolyN = Map[#/.\[CapitalDelta]->\[CapitalDelta]0&,dBlockPoly[l]];
	polynomials[-1]=combineExtFactorAndDeriv[Lambda,OddQ,extFactors,dBlockPolyN];
	polynomials[1]=combineExtFactorAndDeriv[Lambda,EvenQ,extFactors,dBlockPolyN];
	
	(*poleZeroCanceled = DeleteCases[
		polesAssociation[l],
		x_/;Abs[x-\[CapitalDelta]0]<10^-5
	];*)
	
	functionalsPoly = Table[
		(deriv)->Flatten[Table[
			matO2SU4[[idxEqn,idxChn]]*
				polynomials[signO2SU4[[idxEqn]] ][deriv]/
				(Times@@(\[CapitalDelta]0-polesAssociation[l])),
		{idxEqn,9}],1],
	{deriv,{{0,0},{1,0},{2,0}}}]//Association
	
	
	
	
]


ClearAll[computeVac]
computeVac[(*rep_,*)
	Lambda_,polesAssociation_,dBlockPoly_,extFactors_]:=Block[
	{idxChn=repsIdx[{so2[S],su4[0]}],l=0,d=3,shift,
	polynomials,\[CapitalDelta]0,
	dBlockPolyN,functionalsPoly,poleZeroCanceled},
	
	(*shift=0-(l+d-2);*)
	\[CapitalDelta]0 = 0;
	dBlockPolyN = Map[#/.\[CapitalDelta]->\[CapitalDelta]0&,dBlockPoly[l]];
	(*KeySelect[N/@dBlockPolyN,#[[3]]\[Equal]1&]//Print;*)
	polynomials[-1]=combineExtFactorAndDeriv[Lambda,OddQ,extFactors,dBlockPolyN];
	polynomials[1]=combineExtFactorAndDeriv[Lambda,EvenQ,extFactors,dBlockPolyN];
	
	(*poleZeroCanceled = DeleteCases[
		polesAssociation[l],
		x_/;Abs[x-x0]<10^-5
	];*)
	
	functionalsPoly = Table[
		(deriv)->Flatten[Table[
			matO2SU4[[idxEqn,idxChn]]*
				polynomials[signO2SU4[[idxEqn]] ][deriv]/
				(Times@@(\[CapitalDelta]0-polesAssociation[l])),
		{idxEqn,9}],1],
	{deriv,{{0,0},{1,0},{2,0}}}]//Association
	
	
	
	
]


(* ::Section:: *)
(*Interior point method*)


(* ::Subsection:: *)
(*compute y vector*)


computeInitialYVector[
	xBVecByChn_,xFVec_,chnIdxU_,
	deltaXVecByChn_,wVecByChn_,
	aBVec_,aFVec_,aUVec_,
	zVec_,
	\[Xi]Vec_,\[Eta]Vec_,
	c\[Mu]Vec_,c\[Sigma]Vec_,
	bulkFunction_,unitarityFunction_]:=Block[
	{wTVecByChn,matAi\[Mu],matBi\[Mu],mat\[CapitalXi]i\[Sigma],(*zVec,*)
		fBDerivs,fFDerivs,fUDerivs,xBVec
	},
	
	wTVecByChn=(Subtract@@@Partition[Append[#,0],2,1])&/@wVecByChn;
	
	xBVec = KeyValueMap[Function[{rep,states},{#,rep}&/@states],xBVecByChn]//Flatten[#,1]&;
	fBDerivs=Merge[bulkFunction/@xBVec,Identity];
	fFDerivs=Merge[bulkFunction/@xFVec,Identity];
	fUDerivs=Merge[unitarityFunction/@chnIdxU,Identity];
	
	matAi\[Mu]=-Join[ fBDerivs[{0,0}],fFDerivs[{0,0}],fUDerivs[{0,0}] ]//Transpose;
	matBi\[Mu]=-MapThread[Times,{aBVec,fBDerivs[{0,1}]}]//Transpose;
	mat\[CapitalXi]i\[Sigma]=-{aBVec . fBDerivs[{1,0}]+aFVec . fFDerivs[{1,0}]+aUVec . fUDerivs[{1,0}]}//Transpose;
	
	(*zVec = Join[zBVec,zFVec,zUVec];*)
	
	LeastSquares[
		Join[
			matAi\[Mu]//Transpose,
			matBi\[Mu]//Transpose,
			mat\[CapitalXi]i\[Sigma]//Transpose],
		Join[
			-zVec,
			-Flatten[wTVecByChn]+c\[Mu]Vec,
			-\[Eta]Vec+c\[Sigma]Vec]
	]
]


(* ::Subsection:: *)
(*make c vector*)


ClearAll[generateCVecs]
generateCVecs[targetAssociation_,chnToIdxMap_,xBVec_]:=Block[
{c\[Mu]Vec,c\[Sigma]Vec,\[CapitalDelta]MHalfTarget},
	c\[Mu]Vec = - SparseArray[
		KeyMap[
			FirstPosition[xBVec[[;;,2]],#][[1]]&,
			KeySelect[
				KeyMap[chnToIdxMap,targetAssociation],
				!MissingQ[#]& ]
		]//Normal,
		{Length[xBVec]}
	];
	\[CapitalDelta]MHalfTarget = If[MissingQ[#],0,-#]&@targetAssociation["\[CapitalDelta]MHalf"];
	c\[Sigma]Vec = SparseArray[{\[CapitalDelta]MHalfTarget}];
	{c\[Mu]Vec,c\[Sigma]Vec}
]


(* ::Subsection:: *)
(*make gap function*)


generateGapFunction[customGapsAssociation_,chnToIdxMap_,\[Delta]gaps_]:=Block[
{gapFunction,chns,d=3},
	gapFunction = KeyValueMap[
		#2->If[#1[[2]]==0,\[Delta]gaps, \[Delta]gaps ]&, 
		chnToIdxMap ]//Association;
	KeyValueMap[ 
		(gapFunction[chnToIdxMap@#1] = 
			#2 - If[#1[[2]]==0,1/2(d-2),#1[[2]]+(d-1) ])&, 
		customGapsAssociation ];
	gapFunction
]


(* ::Subsection:: *)
(*initialize vectors*)


ClearAll[initializeVectors]
SetAttributes[initializeVectors,HoldFirst];
Options[initializeVectors]={
	generateInitialAVector->False,
	generateInitialYVector->False
}
initializeVectors[
	{xBVecByChn_,xFVec_,chnIdxU_,wVecByChn_,
	aBVec_,aFVec_,aUVec_,
	zVec_,
	\[Xi]Vec_,\[Eta]Vec_,
	c\[Mu]Vec_,c\[Sigma]Vec_,
	yVec_,bVec_,MuOut_},
	(* iniXB and iniAB must be in one-to-one correspondence *)
	iniXB_,iniAB_,
	(* iniXF and iniAF must be in one-to-one correspondence *)
	iniXF_,iniAF_,
	(* chnIdxU and iniAU must be in one-to-one correspondence *)
	iniXU_,iniAU_,
	(* currently, iniE = {initial\[CapitalDelta]Mhalf} *)
	iniE_,
	iniY_,
	Mu_,
	chnToIdxMap_,
	(* gapFunction[chnIdx_] takes the preset index of a channel and returns the gap on the channel *)
	gapFunction_,
	targetAssociation_,
	(* bulkFunction[\[CapitalDelta]_,chnIdx_] takes the dim and channel index of a bulk operator, and returns the association of f(x) and derivatives *)
	bulkFunction_,
	(* unitarityFunction[chnIdx_] takes the index of an unitarity channel, and returns the association of f(x) and derivatives *)
	unitarityFunction_,
	vac_,
	OptionsPattern[]
]:=Block[
{
	xBVec,zBVec,zFVec,zUVec,
	deltaXVecByChn,
	posOverSaturated,
	chnsExisting,chns,d=3
	
},
	If[OptionValue[generateInitialAVector],
		{aBVec,aFVec,aUVec} = computeInitialAVector[
				iniXB,iniXF,iniXU,bulkFunction,unitarityFunction],
		{xBVec,aBVec}=SortBy[Thread[{iniXB,iniAB}],{#[[1,2]]&,#[[1,1]]&}]//Transpose;
		(* fixed channels, unitarity channels *)
		{xFVec,aFVec} = {iniXF,iniAF};
		aUVec = iniAU
	];
	MuOut=Mu;
	xBVecByChn=GroupBy[xBVec,Last][[;;,;;,1]];
	chnsExisting=Keys[xBVecByChn];
	chns=Keys[chnToIdxMap];
	chnIdxU = iniXU;
	(* compute vector x - xBound, and vector w. 
		Add a small shift to x[mu] that marginally exceeds the bound *)
	deltaXVecByChn=KeyValueMap[
		Prepend[#2//Differences,#2[[1]]-(gapFunction[#1])]&,
		xBVecByChn
	];
	posOverSaturated = Position[deltaXVecByChn-Mu,_?Negative];
	xBVecByChn = MapAt[#+Mu&,xBVecByChn,posOverSaturated];
	deltaXVecByChn=KeyValueMap[
		#1->Prepend[#2//Differences,#2[[1]]-(gapFunction[#1])]&,
		xBVecByChn
	]//Association;
	wVecByChn=Mu/deltaXVecByChn;
	(*wTVecByChn=(Subtract@@@Partition[Append[#,0],2,1])&/@wVecByChn;*)
	
	(* Add a small shift to a[mu] that marginally exceeds the bound *)
	posOverSaturated = Position[aBVec-Mu,_?Negative];
	aBVec = MapAt[#+Mu&,aBVec,posOverSaturated];
	posOverSaturated = Position[aFVec-Mu,_?Negative];
	aFVec = MapAt[#+Mu&,aFVec,posOverSaturated];
	posOverSaturated = Position[aUVec-Mu,_?Negative];
	aUVec = MapAt[#+Mu&,aUVec,posOverSaturated];
	(* compute vectors z *)
	zBVec=Mu/aBVec;
	zFVec=Mu/aFVec;
	zUVec=Mu/aUVec;
	zVec=Join[zBVec,zFVec,zUVec];

	(* xi and the conjugate eta *)
	\[Xi]Vec=iniE;
	\[Eta]Vec=Mu/(\[Xi]Vec-1/2(d-2));
	
	(* c vectors *)
	{c\[Mu]Vec,c\[Sigma]Vec} = generateCVecs[targetAssociation,chnToIdxMap,xBVec];
	
	(* b vector *)
	bVec = {vac[{0,0}],vac[{1,0}],vac[{2,0}]};
	
	(* load initial vector y *)
	If[OptionValue[generateInitialYVector],
		yVec = computeInitialYVector[
			xBVecByChn,xFVec,chnIdxU,
			deltaXVecByChn,wVecByChn,
			aBVec,aFVec,aUVec,
			zVec,
			\[Xi]Vec,\[Eta]Vec,
			c\[Mu]Vec,c\[Sigma]Vec,
			bulkFunction,unitarityFunction],
		yVec = iniY
	];
	
]


(* ::Subsection:: *)
(*update matrices*)


ClearAll[updateMatrices]
SetAttributes[updateMatrices,HoldFirst];
updateMatrices[
{(* these variables will be updated: *)
	deltaXVecByChn_,wTVecByChn_,
	matAi\[Mu]_,matBi\[Mu]_,mat\[CapitalXi]i\[Sigma]_,
	h1Vec_,h2Vec_,matJax_,matJa\[Xi]_,matJxx_,matJx\[Xi]_,matJ\[Xi]\[Xi]_,
	matSw_,matTw_,matTx_,
	matSz_,matTz_,matTa_,
	matS\[Eta]_,matT\[Eta]_,matT\[Xi]_
},
(* these variables are updates *)
{aBVec_,aFVec_,aUVec_},zVec_,
{xBVecByChn_,xFVec_},wVecByChn_,
\[Xi]Vec_,\[Eta]Vec_,
yVec_,bVec_,
chnIdxU_,
(* gapFunction[chnIdx_] takes the preset index of a channel and returns the gap on the channel *)
gapFunction_,
(* bulkFunction[\[CapitalDelta]_,chnIdx_] takes the dim and channel index of a bulk operator, and returns the association of f(x) and derivatives *)
bulkFunction_,
(* unitarityFunction[chnIdx_] takes the index of an unitarity channel, and returns the association of f(x) and derivatives *)
unitarityFunction_
]:=Block[
{
	nPB=Length[aBVec],nPF=Length[aFVec],nPU=Length[aUVec],nPE=1,
	xBVec,aVec,
	fBDerivs,fFDerivs,fUDerivs
	(*deltaXVecByChn,wTVecByChn,
	matAi\[Mu],matBi\[Mu],mat\[CapitalXi]i\[Sigma],
	h1Vec,h2Vec,matJax,matJa\[Xi],matJxx,matJx\[Xi],
	matSw,matTw,matTx,
	matSz,matTz,matTa,
	matS\[Eta],matT\[Eta],matT\[Xi],matJ\[Xi]\[Xi]*)
},
	xBVec = KeyValueMap[Function[{rep,states},{#,rep}&/@states],xBVecByChn]//Flatten[#,1]&;
	fBDerivs=Merge[bulkFunction/@xBVec,Identity];
	fFDerivs=Merge[bulkFunction/@xFVec,Identity];
	fUDerivs=Merge[unitarityFunction/@chnIdxU,Identity];
	aVec = Join[aBVec,aFVec,aUVec];
	
	deltaXVecByChn=KeyValueMap[
		#1->Prepend[#2//Differences,#2[[1]]-(gapFunction[#1])]&,
		xBVecByChn
	]//Association;
	wTVecByChn=(Subtract@@@Partition[Append[#,0],2,1])&/@wVecByChn;
	
	matAi\[Mu]=-Join[ fBDerivs[{0,0}],fFDerivs[{0,0}],fUDerivs[{0,0}] ]//Transpose//SparseArray;
	matBi\[Mu]=-MapThread[Times,{aBVec,fBDerivs[{0,1}]}]//Transpose//SparseArray;
	mat\[CapitalXi]i\[Sigma]=-{ aBVec . fBDerivs[{1,0}]
				+aFVec . fFDerivs[{1,0}]
				+aUVec . fUDerivs[{1,0}]
				+bVec[[2]]
			}//Transpose//SparseArray;
	
	h1Vec=-fBDerivs[{0,1}] . yVec;
	matJax=SparseArray[{Band[{1,1}]->h1Vec},{nPB+nPF+nPU,nPB}];
	matJa\[Xi]=-{Join[
				fBDerivs[{1,0}] . yVec,
				fFDerivs[{1,0}] . yVec,
				fUDerivs[{1,0}] . yVec]
			}//SparseArray//Transpose;
	h2Vec=(-fBDerivs[{0,2}] . yVec)*aBVec;
	matJxx=SparseArray[{Band[{1,1}]->h2Vec},{nPB,nPB}];
	matJx\[Xi]={(-fBDerivs[{1,1}] . yVec)*aBVec}//SparseArray//Transpose;
	matJ\[Xi]\[Xi]=SparseArray[{{  -(
							aBVec . fBDerivs[{2,0}] . yVec
							+aFVec . fFDerivs[{2,0}] . yVec
							+aUVec . fUDerivs[{2,0}] . yVec
							+bVec[[3]] . yVec
			)  }}];
	matSz=SparseArray[{Band[{1,1}]->1},{nPB+nPF+nPU,nPB+nPF+nPU}];
	matTz=SparseArray[{Band[{1,1}]->zVec},{nPB+nPF+nPU,nPB+nPF+nPU}];
	matTa=SparseArray[{Band[{1,1}]->aVec},{nPB+nPF+nPU,nPB+nPF+nPU}];
	
	matSw=SparseArray[Reap[Block[{idx=1},
			(If[#>1,Sow/@Table[{i,i+1}->-1,{i,idx,idx+#-2}]];
				Sow/@Table[{i,i}->1,{i,idx,idx+#-1}];
				idx+=#)&/@(Length/@xBVecByChn)
		] ][[2,1]] ];
	matTw=SparseArray[Reap[Block[{idx=1},
			(If[Length[#]>1,Sow[Band[{idx+1,idx}]->-Drop[#,1]]];
				Sow[Band[{idx,idx}]->#];
				idx+=Length[#])&/@wVecByChn
		] ][[2,1]] ];
	matTx=SparseArray[{Band[{1,1}]->Join@@deltaXVecByChn}];
	
	matS\[Eta]=SparseArray[{Band[{1,1}]->1},{nPE,nPE}];
	matT\[Eta]=SparseArray[{Band[{1,1}]->\[Eta]Vec},{nPE,nPE}];
	matT\[Xi]=SparseArray[{Band[{1,1}]->\[Xi]Vec},{nPE,nPE}];
]


(* ::Subsection:: *)
(*update vectors*)


ClearAll[updateVectors]
SetAttributes[updateVectors,HoldFirst];
updateVectors[
	{
		{aBVec_,aFVec_,aUVec_},zVec_,
		{xBVecByChn_,xFVec_},wVecByChn_,
		\[Xi]Vec_,\[Eta]Vec_,
		yVec_
	},
	daVec_,dxVec_,d\[Xi]Vec_,dyVec_,dzVec_,dwVec_,d\[Eta]Vec_,
	prec_
]:=Block[
	{nPB=Length[aBVec],nPF=Length[aFVec],nPU=Length[aUVec],
	daBVec,daFVec,daUVec},
	{daBVec,daFVec,daUVec}=splitVector[daVec,{nPB,nPF,nPU}];
	aBVec = SetPrecision[aBVec+daBVec,prec];
	aFVec = SetPrecision[aFVec+daFVec,prec];
	aUVec = SetPrecision[aUVec+daUVec,prec];
	xBVecByChn = SetPrecision[xBVecByChn+splitVector[dxVec,Length/@xBVecByChn],prec];
	zVec = SetPrecision[zVec+dzVec,prec];
	\[Xi]Vec = SetPrecision[\[Xi]Vec+d\[Xi]Vec,prec];
	wVecByChn = SetPrecision[wVecByChn+splitVector[dwVec,Length/@wVecByChn],prec];
	\[Eta]Vec = SetPrecision[\[Eta]Vec+d\[Eta]Vec,prec];
	yVec = SetPrecision[yVec+dyVec,prec];
];


(* ::Section:: *)
(*Solve linear system (still slow)*)


ClearAll[linearSolveLower,linearSolveLowerInternal]
linearSolveLower[l_,vec_,size_]:=Reap[linearSolveLowerInternal[l,vec,size]][[2,1]]//Flatten
linearSolveLowerInternal[l_,vec_,size_]/;Length[l]>size:=Block[
	{l11=l[[;;size,;;size]],ln1,L11Vec1},
	ln1=l[[size+1;;,;;size]];
	Sow[L11Vec1=LinearSolve[l11,vec[[;;size]]]];
	linearSolveLowerInternal[l[[size+1;;,size+1;;]],
		vec[[size+1;;]]-ln1 . L11Vec1,
		size
	]
];
linearSolveLowerInternal[l_,vec_,size_]/;Length[l]<=size:=Sow[LinearSolve[l,vec]];


ClearAll[linearSolveByLU]
linearSolveByLU[mat_,vec_]:=Block[
	{
		n=Length[mat],permMat,
		lu,p,pinv,c,l,u
	},
	{lu,p,c}=LUDecomposition[mat];
	pinv=InversePermutation[p];
	l = (LowerTriangularize[lu,-1]+IdentityMatrix[Length[lu]])//SparseArray;
	u = UpperTriangularize[lu]//SparseArray;
	(*permMat=Table[UnitVector[n,p[[k]]],{k,n}];*)
	permMat=SparseArray[{Band[{1,1}]->1},{n,n}][[p]];
	linearSolveLower[
		Reverse[u//Transpose]//Transpose//Reverse,
		linearSolveLower[l,permMat . vec,50]//Reverse,
		50
	]//Reverse
]


(* ::Section:: *)
(*Utilities*)


splitVector[vec_,split_List]:=Reap[Fold[
	((Sow[#1];#2)&@@TakeDrop[#1,#2])&,
	vec,split
] ][[2,1]]


splitVector[vec_,split_Association]:=AssociationThread[Keys[split]->splitVector[vec,Values[split]]];


maxIndexBy[l_,f_] := SortBy[
    Transpose[{l,Range[Length[l]]}],
    -f[First[#]]&][[1,2]];

(* finds v' such that a . v = First[v'] + a' . Rest[v'] when normalization . a == 1, where a' is a vector of length one less than a *)
(*reshuffleWithNormalization[normalization_, v_] := Module[
    {j = maxIndexBy[normalization, Abs], const},
    const = v[[j]]/normalization[[j]];
    Prepend[Delete[MapThread[#1 - #2*const&,{v,normalization}], j], const]];*)
(*reshuffleWithNormalization[normalization_, v_] := Module[
    {j = maxIndexBy[normalization, Abs], const},
    const = v[[j]]/normalization[[j]];
    Prepend[Delete[v - normalization*const, j], const]];*)
(*reshuffleWithNormalization[normalization_, v_] := Module[
    {j = maxIndexBy[normalization, Abs], const},
    const = v[[j]]/normalization[[j]];
    (*Prepend[Delete[MapThread[#1 - #2*const&,{v,normalization}], j], const]*)
    Prepend[
    Delete[v,j] - SparseArray[{Band[{1,1}]\[Rule]Delete[normalization,j]}].SparseArray[Table[const,Length[normalization]-1]],
    const]
];
    
restoreCoefficients[yVector_,norm_]:=Module[
	{\[Alpha],j=maxIndexBy[norm,Abs],length=Length[norm],shortNorm},
	shortNorm=Delete[norm,j];
	\[Alpha]=Array[#/.{i_:>yVector[[i]]/;i<j,i_:>yVector[[i-1]]/;i>j,i_:>(1-yVector.shortNorm)/norm[[j]]/;i==j}&,length];
	Return[\[Alpha]];
];*)


reshuffleWithNormalizationZero[normalization_, v_] := Module[
    {j = maxIndexBy[normalization, Abs], const},
    const = v[[j]]/normalization[[j]];
    Delete[v,j] - SparseArray[{Band[{1,1}]->Delete[normalization,j]}] . SparseArray[Table[const,Length[normalization]-1]]
];
    
restoreCoefficientsZero[yVector_,norm_]:=Module[
	{\[Alpha],j=maxIndexBy[norm,Abs],length=Length[norm],shortNorm},
	shortNorm=Delete[norm,j];
	\[Alpha]=Array[#/.{i_:>yVector[[i]]/;i<j,i_:>yVector[[i-1]]/;i>j,i_:>(-yVector . shortNorm)/norm[[j]]/;i==j}&,length];
	Return[\[Alpha]];
];
