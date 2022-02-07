# Automated Robustness Verification
We present some additional information in this file to explain concepts in the
paper in further detail.

## Encoding execution graphs using SMT
Our verification approach relies on using execution graphs to represent
program executions. We search for the existence of a robustness violating
witness in these executions graphs using SMT solvers which denotes that the
program is not robust. The absence of any such witness denotes that the
program is robust. In the following paragraphs, we explain the salient
features of our encoding.

We use uninterpreted sorts to represent events, values, invocations and
sessions. Constants of sort `E` are used to represent events. Other
constants are used to denote constraints on values, invocations and
sessions.

```smt2
(declare-sort E) ; Sort for events
(declare-sort I) ; Sort for invocations
(declare-sort V) ; Sort for values
(declare-sort S) ; Sort for sessions
```

We use some inductive datatypes to ascribe information to each event such
as the location accessed, value accessed and access type -

```
(declare-datatypes () ((EventType R W U F)))              ; Type of access
(declare-datatypes () ((EventLabel Rlx Rel Acq AcqRel)))  ; Access memory order
(declare-datatypes () ((Field Val Next)))                 ; Access location 
```

We then define uninterpreted functions which are used to ascribe information
to each event. Some examples of such functions, which denote the type and
memory order of each event are as follows -

```smt2
(declare-fun etype  (E) EventType)  ; Mapping every event to its access type
(declare-fun elabel (E) EventLabel) ; Mapping every event to its memory order
```

Finally, we use binary predicates to encode the relations which denote an
exeuction graph -

```smt2
(declare-fun so   (E E) Bool) ; session order
(declare-fun rf   (E E) Bool) ; reads from 
(declare-fun mo   (E E) Bool) ; memory order
(declare-fun sw   (E E) Bool) ; synchronizes with
(declare-fun fr   (E E) Bool) ; from reads
(declare-fun hb   (E E) Bool) ; happens before
(declare-fun hbSC (E E) Bool) ; happens before (sequential consistency)
```

For each relation, we also declare the constraints necessary. For example, the
`mo` relation should be a total order for all locations -

```smt2
(assert (forall ((e1 E) (e2 E)) ; for all events e1, e2
  (=> (mo e1 e2)                ; mo e1 e2 implies 
      (not (mo e2 e1))))        ; not (mo e2 e1)

(assert (forall ((e1 E) (e2 E) (e3 E)) ; for all events e1, e2, e3
  (=> (and (mo e1 e2) (mo e2 e3))      ; (mo e1 e2) and (mo e2 e3) implies
      (mo e1 e3))))                    ; (mo e1 e3)
```

We also have additional constraints for each relation consistent with our
implementation such as reads-from should relate a read and a write or that
session order should exist between all events in a particular session.

Given this SMT encoding, a satisfiable model for this instance of formulas
represents a possible program execution. For example, a simple example would be
represented as - #TODO insert graph

With this encoding, it becomes possible to pose the following robustness query
for a given exeuction graph, where `e1` and `e2` are instantiated to specific
events (which we will discuss in the following sections) - 

```smt2
(assert (=> (hbSC e1 e2) (not hb e1 e2)))
```

## Detailed explanation of Treiber stack
We first present the code for a Treiber stack implementation that we have
considered for verification. This library implementation has two methods
as follows -

```c {.line-numbers}
void push(int v) {
  node* n = malloc(sizeof(node)); 
  atomic_store_explicit(&(n->val), v , memory_order_relaxed);
  while(true) {
    node* t = atomic_load_explicit(top, memory_order_relaxed);
    atomic_store_explicit(&(n->next), t, memory_order_relaxed);
    if (atomic_compare_exchange_strong_explicit(top, t, n, memory_order_acqrel)) // LP, push
      break;
  }
}

int pop() {
  while(true) {
    node* t = atomic_load_explicit(top, memory_order_acquire);
    if (t == NULL) {
      return EMPTY; // LP, pop
    }
    int v = atomic_load_explicit(&(t->val), memory_order_relaxed);
    node* n = atomic_load_explicit(&(t->next), memory_order_relaxed);
    if(atomic_compare_exchange_string_explicit(top, t, n, memory_order_acqrel)) // LP, pop
      return v;
  }
}
```

The comments of the form `LP, push` and `LP, pop` denote that these points are
linearization points corresponding to a certain method. Given that these
linearization points can be non-local to a given method, the method annotation
allows us to track the method to which the linearization point belongs. The
programmer also provides a specification file of the form - #TODO

Given that the CAS operations can arbitrarily fail, these methods would
generate an infinite number of events. But a robustness-preserving
transformation allows us to reason about the behavior of these methods using a
finite number of events. The transformed program is as follows -

```
void push(int v) {
  node* n = malloc(sizeof(node));
  atomic_store_explicit(&(n->val), v , memory_order_relaxed);
  node* t = atomic_load_explicit(top, memory_order_relaxed);
  atomic_store_explicit(&(n->next), t, memory_order_relaxed);
  bcas_explicit(top, t, n, memory_order_acqrel);
}

int pop() {
  node* t = atomic_load_explicit(top, memory_order_acquire);
  if (t == NULL) {
    return EMPTY;
  }
  int v = atomic_load_explicit(&(t->val), memory_order_relaxed);
  node* n = atomic_load_explicit(&(t->next), memory_order_relaxed);
  bcas_explicit(top, t, n, memory_order_acqrel);
  return v;
}
```

Notice that we have replaced the CASs with blocking CAS operations which we
denote as `bcas_explicit` in the code. This removes the while loop, as the
`bcas` operation means that the CAS blocks until it succeeds, thus removing
the need for a retry loop. This relies on the assumption that the failing
CAS events do not have any visible effects, thus can be ignored.

Once this transformation is done, our code generates the events for each


Given that there are 3 location classes in the Treiber Stack namely - `Top`,
`Next` and `Val`, we have the following set of cases that we need to verify.

| Case | L   | L'  |
|------|-----|-----|
|   1  | Top | Top |
|   2  | Top | Next|
|   3  | Top | Val |
|   4  | Next| Top |
|   5  | Next| Next|
|   6  | Next| Val |
|   7  | Val | Top |
|   8  | Val | Next|
|   9  | Val | Val |

## Detailed explanation of Lock-free queue

## Detailed explanation of Non-blocking set
