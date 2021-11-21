/* interface SetCounter */
SetCounter = Rec SelfType .
  { get : SelfType -> Nat,
    inc : SelfType -> Unit,
    set : SelfType -> Nat -> Unit,
    reset : SelfType -> Unit };
    
stubSimple = 
  fold[SetCounter] 
    { get = lambda s:SetCounter . 0,
      inc = lambda s:SetCounter . unit,
      set = lambda s:SetCounter . lambda n:Nat . unit,
      reset = lambda s:SetCounter . unit };
        
         
SimpleRep = { val : Ref Nat };

/* alloc makes new representation object (fields) */
allocSimple = lambda _:Unit . { val = ref 0 } as SimpleRep;

/* class takes rep and initializes and creates interface */
classSimple = lambda r:SimpleRep .
  stubSimple; /* TODO */
      
/* constructor takes rep and updates rep by side-effect */
newSimple = lambda r:SimpleRep .
  unit; /* No change */
  
/* make takes constructor args (if any) and returns new initialized object */
makeSimple = lambda _:Unit .
  let r = allocSimple unit in
    (newSimple r; classSimple r);


InitialRep = { val : Ref Nat, init : Ref Nat };

/* alloc makes new representation object (fields) */
allocInitial = lambda _:Unit . { val = ref 0, init = ref 0 } as InitialRep;

/* class takes rep and initializes and creates interface. */
classInitial = lambda r:InitialRep.
  let super = unfold[SetCounter] (classSimple r) in
    stubSimple; /* TODO */

/* constructor takes rep and constructor args and updates rep */
newInitial = lambda r:InitialRep . lambda v:Nat .
  (newSimple r; /* super constructor call */
   r.val := v;
   r.init := v);
  
makeInitial = lambda v:Nat .
  let r = allocInitial unit in
    (newInitial r v;
     classInitial r);
  
  
BackupRep = InitialRep;

allocBackup = lambda _:Unit . allocInitial unit;

classBackup = lambda r:BackupRep .
  let super = unfold[SetCounter] (classInitial r) in
    stubSimple; /* TODO */
     
newBackup = lambda r:BackupRep .
  newInitial r 6;

makeBackup = lambda _:Unit .
  let r = allocBackup unit in
    (newBackup r;
     classBackup r);

    
get = lambda s:SetCounter . (unfold[SetCounter] s).get(s);
set = lambda s:SetCounter . lambda nv : Nat . (unfold[SetCounter] s).set(s)(nv);
inc = lambda s:SetCounter . (unfold[SetCounter] s).inc(s);
reset = lambda s:SetCounter . (unfold[SetCounter] s).reset(s);

equal = fix (lambda eq: Nat -> Nat -> Bool .
               lambda m: Nat .
                 lambda n:Nat .
                    if iszero m then iszero n else
                    if iszero n then false else eq (pred m) (pred n));
       
"We create some simple counters";
                  
c1 = makeSimple unit;
c2 = makeSimple unit;

"Next few tests should return 0, unit, 1, 0, unit, 1, unit, 4, 1, unit, 0, unit, 0";

get c1;
inc c1;
get c1;
get c2;
inc c2;
get c2;
set c2 4;
get c2;
get c1;
reset c2;
get c2;
reset c1;
get c1;

"Now we create some initial counters";

c1 = makeInitial 2;
c2 = makeInitial 1;

"New few tests should return 2, unit, 3, 1, unit, 2, unit, 4, 3, unit, 1, unit, 2";

get c1;
inc c1;
get c1;
get c2;
inc c2;
get c2;
set c2 4;
get c2;
get c1;
reset c2;
get c2;
reset c1;
get c1;

"Now some Backup Counters";

c1 = makeBackup unit;
c2 = makeBackup unit;

"New few tests should return 6, unit, 7, 6, unit, 7, unit, 4, 7, unit, 7, unit, 6";

get c1;
inc c1;
get c1;
get c2;
inc c2;
get c2;
set c2 4;
get c2;
get c1;
reset c2;
get c2;
reset c1;
get c1;

InstrSetCounter = Rec SelfType .
  { get : SelfType -> Nat,
    inc : SelfType -> Unit,
    set : SelfType -> Nat -> Unit,
    reset : SelfType -> Unit,
    acc : SelfType -> Nat };

/* The following doesn't type check: */
test = lambda isc:InstrSetCounter . get(isc);

/* 
 * Explain why we can't add new methods in a sub type 
 */
