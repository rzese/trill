#include <math.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
//#include <nlopt.h>
#include "cudd.h"
#include <SWI-Prolog.h>
#include <unistd.h>
#include <sys/types.h>

#include <assert.h>
#include <locale.h>
#include <time.h>
#include <ctype.h> // isdigit

#define MAP_SIZE 5096

#ifdef _WIN32
#include <Windows.h>
#endif

#define BUFSIZE 200000
#define LOGZERO log(0.01)
#define CACHE_SLOTS 1
#define UNIQUE_SLOTS 1
#define RETURN_IF_FAIL if (ret!=TRUE) return ret;
#define MINUS_INF -100000
#define DEBUG 0
#define PRINT_STEPS 1

// CHANGE THIS
const char *py_path = "home/<user>/.local/share/swi-prolog/pack/bddem/run.py";
const char *differentiate_path = "home/<user>/.local/share/swi-prolog/pack/bddem/differentiate.pl";
//

typedef struct name_indexes {
  int index_bdd;    // this is the index in the bdd
  int index_array;  // this is the index in the array that stores optimal values
  char *name;
} name_indexes;

typedef struct all_data {
  // char to_optimize[MAP_SIZE];
  char *to_optimize;
  char **constraints;
  int n_constraints;
  int n_triples;
  name_indexes *triple; // name - index_b - index_a 
  char *current_constraint; // used to discriminate between constraint or optimize
} all_data;

typedef struct
{
  int nVal,nRule;
  int firstBoolVar;
  int abducible;
  int query;
  int decision;
  int optimize;
} variable;

typedef struct {
  double prob_tr;
  double prob_f;
  double p_ev_false;
  double p_ev_true;
} infl_table;

typedef struct {
  int n_values;
  infl_table *tab;
} inf_tab;

typedef struct {
  int index;
  int mode; // 0 false, 1 true
} couple;

// indexed on single node
typedef struct {
  int n_nodes;
  double prob;
  couple *nodes;
} path;

typedef struct {
  int n_paths;
  int n_vars;
  int comp;
  path* paths_list;
} paths_table;

typedef struct {
  int n_nodes;
  paths_table *tables;
} computed_paths_table;

// ======================
// RICCARDO
// indexed on single node
typedef struct {
  int n_nodes;
  double prob;
  int *nodes;
} just;

typedef struct {
  int n_justs;
  int n_vars;
  int comp;
  just* justs_list;
} justs_table;

// RICCARDO qua ho l'elemento della tabella, quindi corrispondenza nodo <-> paths_table
typedef struct
{
  DdNode *key;
  justs_table value;
} computed_justs_table_el;

// RICCARDO qua ho preso la computed_paths_table e ho aggiunto un ulteriore livello, la riga computed_just_table_el seguendo tablerow e rowel
typedef struct {
  int n_nodes;
  computed_justs_table_el *row;
} computed_justs_table;

// ======================

typedef struct
{
  DdNode *key;
  double value;
} rowel;

typedef struct
{
  int cnt;
  rowel *row;
} tablerow;


typedef struct environment
{
  DdManager * mgr; //Cudd manager
  int * bVar2mVar; //array that maps Boolean vars to multi-valued vars
  variable * vars; // multivalued variables
  int nVars;  // number of multivalued variables
  double * probs; // probabilities of Boolean variables
  int  boolVars;  // number of Boolean variables
  int nRules;  // number of rules
  int * rules; // array with the number of head atoms for each rule
  int n_abd;
  int n_abd_boolVars;
  int n_opt_boolVars;
  int n_opt;
} environment;

typedef struct
{
  environment * env; // one environment for each example
  int ex;  // number of examples
  double * sigma; // sigma array for taking into account deleted paths
  double ***eta;  // eta array: for each rule, each Bool var stores two doubles
  double ***eta_temp; // eta array storing the contribution of the current example
  int * rules; // array with the number of head atoms for each rule
  int * tunable_rules; // array with 1 if the parameters of the rule are tunable, 0 otherwise
  int nRules; // number of rules
  double **arrayprob; //value of paramters. One value ofr each rule and Bool var
  double * nodes_probs;
  tablerow * nodesB; // tables of probabilities for nodes in Backward step
  tablerow * nodesFE; // tables of probabilities for nodes in Forward step
  tablerow * nodesFO; // tables of probabilities for nodes in Forward step
  double * example_prob; // probability (frequency) of examples in the data
  double alpha; // type of parameter initialization in EM: 
                // 0 for truncated Dirichlet process
                // >0 for symmetric Dirichlet distribution with values alpha
} example_data;

typedef struct
{
  int var,val;
} assign;

typedef struct explan
{
  assign a;
  struct explan * next;
} explan_t;

typedef struct
{
  double prob;
  explan_t * mpa;
} prob_abd_expl;

typedef struct
{
  double prob;
  assign *mpa;
} prob_abd_expl_array;


typedef struct
{
  DdNode *node;
  int comp;
} explkey;

typedef struct
{
  explkey key;
  prob_abd_expl value;
} explrowel;

typedef struct
{
  int cnt;
  explrowel *row;
} expltablerow;

// structure representing
// the root of the add and
// the min and max terminal
typedef struct {
  DdNode *root;
  double impact;
} node_impact;

static foreign_t ret_prob(term_t,term_t,term_t);
static foreign_t ret_abd_prob(term_t,term_t,term_t,term_t);
//static foreign_t ret_opt_prob(term_t, term_t, term_t, term_t, term_t, term_t, term_t, term_t, term_t, term_t);
static foreign_t ret_map_prob(term_t,term_t,term_t,term_t);
static foreign_t ret_vit_prob(term_t arg1, term_t arg2,
  term_t arg3, term_t arg4);
double Prob(DdNode *node,environment *env,tablerow *table);
prob_abd_expl abd_Prob(DdNode *node,environment *env,expltablerow *expltable,
  tablerow *table,
  int comp_par);
prob_abd_expl map_Prob(DdNode *node, environment * env,
    expltablerow * maptable, tablerow * table,
    int comp_par);
prob_abd_expl vit_Prob(DdNode *node, environment * env,
  expltablerow * expltable, tablerow * table,
  int comp_par);
static foreign_t end_ex(term_t);
static foreign_t init(term_t);
static foreign_t end(term_t arg1);
static foreign_t init_ex(term_t arg1, term_t arg2);
static foreign_t add_var(term_t,term_t,term_t,term_t);
static foreign_t add_query_var(term_t,term_t,term_t,term_t);
static foreign_t add_abd_var(term_t,term_t,term_t,term_t);
static foreign_t add_opt_var(term_t,term_t,term_t,term_t);
static foreign_t init_em(term_t);
static foreign_t end_em(term_t);
static foreign_t EM(term_t,term_t,term_t,term_t,
  term_t,term_t,term_t,term_t,term_t);
static foreign_t reorder(term_t arg1);
static foreign_t make_query_var(term_t arg1, term_t arg2, term_t arg3);


static foreign_t init_par(example_data * ex_d, term_t ruleHeadsTerm);
double ProbPath(example_data * ex_d,DdNode *node, int nex);
//static int rec_deref(void);
void Forward(example_data * ex_d,DdNode *node, int nex);
void UpdateForward(example_data * ex_d,DdNode * node, int nex,
  DdNode *** nodesToVisit,int * NnodesToVisit);
double GetOutsideExpe(example_data *ex_d,DdNode *root,double ex_prob, int nex);
void Maximization(example_data * ex_d);
static double Expectation(example_data *ex_d,DdNode **nodes_ex, int lenNodes);
int reorder_int(environment *env);

FILE *open_file(char *filename, const char *mode);
tablerow* init_table(int varcnt);
double * get_value(tablerow *tab,  DdNode *node);
void add_or_replace_node(tablerow *tab, DdNode *node, double value);
void add_node(tablerow *tab, DdNode *node, double value);
void destroy_table(tablerow *tab,int varcnt);
expltablerow* expl_init_table(int varcnt);
prob_abd_expl * expl_get_value(expltablerow *tab,  DdNode *node, int comp);
void expl_add_node(expltablerow *tab, DdNode *node, int comp, prob_abd_expl value);
void expl_destroy_table(expltablerow *tab,int varcnt);
DdNode* get_node(DdNode *node,tablerow *tab);

install_t install(void);
void write_dot(environment * env, DdNode * bdd, FILE * file);

explan_t * insert(assign assignment,explan_t * head);
explan_t * duplicate(explan_t * head);
void free_list(explan_t * head);

term_t clist_to_pllist(explan_t *mpa, environment * env);
term_t abd_clist_to_pllist(explan_t *mpa);
term_t vit_clist_to_pllist(explan_t *mpa, environment * env);


double uniform_sample();
double gauss_sample(double mean,double var);
double gamma_sample(double shape, double scale);
double gamma_sample_gt1(double shape);
void dirichlet_sample(double * alpha,int K, double * theta);
void symmetric_dirichlet_sample(double alpha,int K, double * theta);

static foreign_t gamma_sample_pl(term_t arg1,term_t arg2,term_t arg3);
static foreign_t gauss_sample_pl(term_t arg1,term_t arg2,term_t arg3);
static foreign_t uniform_sample_pl(term_t arg1);
static foreign_t dirichlet_sample_pl(term_t arg1,term_t arg2);
static foreign_t symmetric_dirichlet_sample_pl(term_t arg1,term_t arg2, term_t arg3);
static foreign_t discrete_sample_pl(term_t arg1,term_t arg2);
static foreign_t initial_values_pl(term_t arg1, term_t arg2);

DdNode* Probability_dd(environment *env, DdNode *current_node, tablerow *table);
DdNode* Probability_dd_bdd(environment *env, DdNode *current_node);
void traverse_tree(DdNode *node, DdNode **bestNode, int *index, double *value);
void traverse_tree_depth_bound(DdNode *node, DdNode **bestNode, int *index, double *value, int current_lv, int max_lv, int precise);
int find_path(DdNode *node, double value, int **array, int *len);
void debug_cudd_env(environment *env, int i);
void dump_var(variable *var);
void dump_env(environment *env);
int compare_utils(const void *a, const void *b);
DdNode *setLowerBound(DdManager *dd, DdNode *current_node, double lowerBound);
static foreign_t add_decision_var(term_t env_ref, term_t rule,term_t var_out);
static foreign_t probability_dd(term_t env_ref, term_t bdd_ref, term_t add_out);
static foreign_t add_prod(term_t env_ref, term_t add_in, term_t value, term_t add_out);
static foreign_t add_sum(term_t env_ref, term_t add_A, term_t add_B, term_t add_out);
static foreign_t ret_strategy(term_t env_ref, term_t add_A, term_t strategy_list, term_t cost);
static foreign_t compute_best_strategy(term_t env_ref, term_t b_list, term_t u_list, term_t strategy_list, term_t cost);
static term_t debug_cudd_var(term_t env_ref, term_t out_null);
void print_prob_abd_expl(prob_abd_expl *pae);
void print_abd_explan(explan_t *et);
int in_list(explan_t *list, assign element);
explan_t *merge_explain(explan_t *a, explan_t *b);

static foreign_t ret_influence_prob(term_t env_ref, term_t root, term_t prob_out, term_t influence_table);
// static foreign_t ret_paths_prob(term_t env_ref, term_t root, term_t prob_out, term_t paths_t, term_t probs_t);
// static foreign_t ret_prob_constr(term_t env_ref, term_t root, term_t objective, term_t mode, term_t constraintsList, term_t assigments);
double Prob_influence(DdNode *node, environment *env, tablerow *table, infl_table *infl_t);
// double Prob_paths(DdNode *node, environment *env, tablerow *table, all_paths_table *p_tab, int root_index); 
double evaluate_or_derivate_function(const char *predicate, int arity, char *function, char *variables, char *variable);
char *from_paths_to_sym_eq(paths_table *table, environment *env, all_data *opt_data, int *malloc_size); 



static foreign_t uniform_sample_pl(term_t arg1)
{
  double sample;
  int ret;
  term_t out;

  sample=uniform_sample();
  out=PL_new_term_ref();
  ret=PL_put_float(out,sample);
  RETURN_IF_FAIL
  return PL_unify(out,arg1);
}
double uniform_sample()
{
  return ((double)rand())/RAND_MAX;
}

static foreign_t gauss_sample_pl(term_t arg1,term_t arg2,term_t arg3)
{
  double mean, var, sample;
  int ret;
  term_t out;

  ret=PL_get_float(arg1,&mean);
  RETURN_IF_FAIL
  ret=PL_get_float(arg2,&var);
  RETURN_IF_FAIL
  sample=gauss_sample(mean,var);
  out=PL_new_term_ref();
  ret=PL_put_float(out,sample);
  RETURN_IF_FAIL
  return PL_unify(out,arg3);
}

double gauss_sample(double mean,double var)
{
  double u1,u2,r,theta,s; 

  u1= uniform_sample();
  u2= uniform_sample();
  r= sqrt(-2*log(u1));
  theta=2*M_PI*u2;
  s=r*cos(theta);
  return sqrt(var)*s+mean;
}
static foreign_t gamma_sample_pl(term_t arg1,term_t arg2,term_t arg3)
{
  double shape, scale, sample;
  int ret;
  term_t out;

  ret=PL_get_float(arg1,&shape);
  RETURN_IF_FAIL
  ret=PL_get_float(arg2,&scale);
  RETURN_IF_FAIL
  sample=gamma_sample(shape,scale);
  out=PL_new_term_ref();
  ret=PL_put_float(out,sample);
  RETURN_IF_FAIL
  return PL_unify(out,arg3);
}
double gamma_sample(double shape, double scale)
{
  double u,s;
  if (shape>=1)
    return gamma_sample_gt1(shape)*scale;
  else
  {
    u=uniform_sample();
    s=gamma_sample_gt1(shape+1);
    return pow(s*u,1/shape)*scale;
  }
}
double gamma_sample_gt1(double shape)
{
  double c,d,x,v,u;

  d=shape-1.0/3.0;
  c =1.0/sqrt(9.0*d);

  do
  {
    do
    {
      x=gauss_sample(0.0,1.0);
      v=pow(1+c*x,3);
    } while (v<=0);
    u=uniform_sample();
  } while (u>=1-0.0331*pow(x,4) && log(u)>=0.5*pow(x,2)+d*(1-v+log(v)));
  return d*v;
}
static foreign_t symmetric_dirichlet_sample_pl(term_t arg1,term_t arg2, term_t arg3)
{
  double  alpha, * sample;

  int ret, i, K;
  term_t out, head;

  head=PL_new_term_ref();
  out=PL_new_term_ref();

  ret=PL_get_integer(arg2,&K);
  RETURN_IF_FAIL
  sample=malloc(sizeof(double)*K);

  ret=PL_get_float(arg1,&alpha);
  RETURN_IF_FAIL
  symmetric_dirichlet_sample(alpha,K,sample);

  ret=PL_put_nil(out);
  RETURN_IF_FAIL
  for (i=0;i<K;i++)
  {
    ret=PL_put_float(head,sample[i]);
    RETURN_IF_FAIL
    ret=PL_cons_list(out,head,out);
    RETURN_IF_FAIL
  }
  return PL_unify(out,arg3);

}
static foreign_t dirichlet_sample_pl(term_t arg1,term_t arg2)
{
  double * alpha, * sample;

  int ret, i;
  size_t K;
  term_t out,alphaterm, head;


  head=PL_new_term_ref();
  out=PL_new_term_ref();
  alphaterm=PL_copy_term_ref(arg1);
  ret=PL_skip_list(alphaterm,0,&K);
  if (ret!=PL_LIST) return FALSE;
  alpha=malloc(sizeof(double)*K);
  sample=malloc(sizeof(double)*K);

  for (i=0;i<K;i++)
  {
    ret=PL_get_list(alphaterm,head,alphaterm);
    RETURN_IF_FAIL
    ret=PL_get_float(head,&alpha[i]);
    RETURN_IF_FAIL
  }
  dirichlet_sample(alpha,K,sample);
  ret=PL_put_nil(out);
  RETURN_IF_FAIL
  for (i=0;i<K;i++)
  {
    ret=PL_put_float(head,sample[i]);
    RETURN_IF_FAIL
    ret=PL_cons_list(out,head,out);
    RETURN_IF_FAIL
  }
  return PL_unify(out,arg2);

}
static foreign_t discrete_sample_pl(term_t arg1,term_t arg2)
{
  double * theta;
  double u, p;

  int ret, i;
  size_t K;
  term_t out,thetaterm, head;


  head=PL_new_term_ref();
  out=PL_new_term_ref();
  thetaterm=PL_copy_term_ref(arg1);
  ret=PL_skip_list(thetaterm,0,&K);
  if (ret!=PL_LIST) return FALSE;
  theta=malloc(sizeof(double)*K);

  for (i=0;i<K;i++)
  {
    ret=PL_get_list(thetaterm,head,thetaterm);
    RETURN_IF_FAIL
    ret=PL_get_float(head,&theta[i]);    
    RETURN_IF_FAIL
  }
  u=uniform_sample();
  i=0;
  p=theta[0];
  while (u>p && i<K)
  {
    i++;
    p=p+theta[i];
  }
  ret=PL_put_integer(out,i);
  RETURN_IF_FAIL
  free(theta);
  return PL_unify(out,arg2);
}
void symmetric_dirichlet_sample(double alpha,int K, double * theta)
{
  int i;
  double * alphas;

  alphas=malloc(sizeof(double)*K);

  for (i=0;i<K;i++)
    alphas[i]=alpha;
  dirichlet_sample(alphas,K,theta);
  free(alphas);
}

void dirichlet_sample(double * alpha,int K, double * theta)
{
  int i;
  double sum;
  double * gamma;

  gamma=malloc(sizeof(double)*K);

  sum=0.0;
  for (i=0;i<K;i++)
  {
    gamma[i]=gamma_sample(alpha[i],1.0);
    sum=sum+gamma[i];
  }
  for (i=0;i<K;i++)
    theta[i]=gamma[i]/sum;
  free(gamma);
}

static foreign_t init_em(term_t arg1)
{
  int ret;
  example_data * ex_d;

  term_t ex_d_t=PL_new_term_ref();
  ex_d=(example_data *)malloc(sizeof(example_data));

  ex_d->ex=0;
  ex_d->nRules=0;
  ex_d->env=NULL;
  ex_d->eta=NULL;
  ex_d->eta_temp=NULL;
  ex_d->rules=NULL;
  ex_d->nodes_probs=NULL;
  ex_d->tunable_rules=NULL;
  ex_d->arrayprob=NULL;
  ex_d->alpha=0.0;

  ret=PL_put_pointer(ex_d_t,(void *)ex_d);
  RETURN_IF_FAIL
  return(PL_unify(ex_d_t,arg1));

}

static foreign_t initial_values_pl(term_t arg1, term_t arg2)
{
  example_data * ex_d;

  int ret;

  ret=PL_get_pointer(arg1,(void **)&ex_d);
  RETURN_IF_FAIL
  ret=PL_get_float(arg2,&(ex_d->alpha)); // <- MOD arg1 -> arg2
  RETURN_IF_FAIL
  PL_succeed;
}
static foreign_t init_ex(term_t arg1, term_t arg2)
{
  example_data * ex_d;
  DdManager * mgr;
  term_t env_t;
  int ex,ret;

  env_t=PL_new_term_ref();
  ret=PL_get_pointer(arg1,(void **)&ex_d);
  RETURN_IF_FAIL
  ex=ex_d->ex;
  ex_d->env=(environment *) realloc(ex_d->env, (ex+1)*sizeof(environment));
  ex_d->env[ex].mgr=Cudd_Init(0,0,UNIQUE_SLOTS,CACHE_SLOTS,5120);
  mgr=ex_d->env[ex].mgr;
  // Cudd_AutodynEnable(mgr, CUDD_REORDER_GROUP_SIFT);
  Cudd_SetMaxCacheHard(mgr, 0);
  Cudd_SetLooseUpTo(mgr, 0);
  Cudd_SetMinHit(mgr, 15);

  ex_d->env[ex].bVar2mVar=NULL;

  ex_d->env[ex].vars=NULL;

  ex_d->env[ex].nVars=0;

  ex_d->env[ex].probs=NULL;

  ex_d->env[ex].boolVars=0;

  ex_d->env[ex].nRules=ex_d->nRules;

  ex_d->env[ex].rules=ex_d->rules;

  ret=PL_put_pointer(env_t,(void *) (ex_d->env+ex));
  RETURN_IF_FAIL
  return(PL_unify(env_t,arg2));

}

static foreign_t end_ex(term_t arg1)
{
  int ret;
  example_data *ex_d;

  ret=PL_get_pointer(arg1,(void **)&ex_d);
  RETURN_IF_FAIL
  ex_d->ex=ex_d->ex+1;
  PL_succeed;
}

static foreign_t init(term_t arg1)
{
  term_t env_t;
  environment * env;
  int ret;

  env_t=PL_new_term_ref();
  env=(environment *)malloc(sizeof(environment));
  // env->mgr=Cudd_Init(0,0,UNIQUE_SLOTS,CACHE_SLOTS,0);
  env->mgr=Cudd_Init(0,0,CUDD_UNIQUE_SLOTS,CACHE_SLOTS,0);

  Cudd_AutodynEnable(env->mgr, CUDD_REORDER_GROUP_SIFT);
  Cudd_SetMaxCacheHard(env->mgr, 0);
  Cudd_SetLooseUpTo(env->mgr, 0);
  Cudd_SetMinHit(env->mgr, 15);
  // Cudd_SetMaxMemory(env->mgr,8000000);

  env->bVar2mVar=NULL;
  env->vars=NULL;
  env->nVars=0;
  env->probs=NULL;
  env->boolVars=0;
  env->nRules=0;
  env->rules= NULL;
  env->n_abd=0;
  env->n_abd_boolVars=0;
  env->n_opt = 0;
  env->n_opt_boolVars = 0;

  ret=PL_put_pointer(env_t,(void *) env);
  RETURN_IF_FAIL
  return(PL_unify(env_t,arg1));
}

static foreign_t end(term_t arg1)
{
  int ret;
  environment *env;

  ret=PL_get_pointer(arg1,(void **)&env);
  RETURN_IF_FAIL

  // printf("Pre - Cudd_ReadMemoryInUse(env->mgr) = %ld bytes\n",Cudd_ReadMemoryInUse(env->mgr));
  // printf("Cudd_CheckZeroRef(env->mgr) = %d\n",Cudd_CheckZeroRef(env->mgr));
  
  // debug_cudd_env(env,0);
  
  Cudd_Quit(env->mgr);

  free(env->bVar2mVar);
  free(env->vars);
  free(env->probs);
  free(env->rules);
  free(env);

  PL_succeed;
}



static double Expectation(example_data * ex_d,DdNode **nodes_ex,int lenNodes)
{
  int i;
  double rootProb,CLL=0;

  for(i=0;i<lenNodes;i++)
  {
    if (!Cudd_IsConstant(nodes_ex[i]))
    {
      ex_d->nodesB=init_table(ex_d->env[i].boolVars);
      ex_d->nodesFE=init_table(ex_d->env[i].boolVars);
      ex_d->nodesFO=init_table(ex_d->env[i].boolVars);

      Forward(ex_d,nodes_ex[i],i);
      rootProb=GetOutsideExpe(ex_d,nodes_ex[i],ex_d->example_prob[i],i);

      if (rootProb<=0.0)
        CLL = CLL + LOGZERO*ex_d->example_prob[i];
      else
        CLL = CLL + log(rootProb)*ex_d->example_prob[i];

      ex_d->nodes_probs[i]=rootProb;
      destroy_table(ex_d->nodesB,ex_d->env[i].boolVars);
      destroy_table(ex_d->nodesFE,ex_d->env[i].boolVars);
      destroy_table(ex_d->nodesFO,ex_d->env[i].boolVars);
    }
    else
      if (nodes_ex[i]==Cudd_ReadLogicZero(ex_d->env[i].mgr))
      {
        CLL=CLL+LOGZERO*ex_d->example_prob[i];
	ex_d->nodes_probs[i]=0.0;
      }
      else
        ex_d->nodes_probs[i]=1.0;
  }
  return CLL;
}

static foreign_t end_em(term_t arg1)
{
  int r,i,ret;
  example_data * ex_d;
  ret=PL_get_pointer(arg1,(void **)&ex_d);
  RETURN_IF_FAIL

  for (i=0;i<ex_d->ex;i++)
  {
    Cudd_Quit(ex_d->env[i].mgr);
    free(ex_d->env[i].bVar2mVar);
    free(ex_d->env[i].vars);
    free(ex_d->env[i].probs);
  }

  free(ex_d->env);
  for (r=0;r<ex_d->nRules;r++)
  {
    if (ex_d->tunable_rules[r])
    {
      for (i=0;i<ex_d->rules[r]-1;i++)
      {
        free(ex_d->eta[r][i]);
        free(ex_d->eta_temp[r][i]);
      }
      free(ex_d->eta[r]);
      free(ex_d->eta_temp[r]);
    }
  }
  free(ex_d->eta);
  free(ex_d->eta_temp);
  free(ex_d->rules);
  free(ex_d);
  PL_succeed;
}


static foreign_t ret_prob(term_t arg1, term_t arg2, term_t arg3)
{
  term_t out;
  environment * env;
  DdNode * node;
  tablerow * table;
  double prob;
  int ret;

  ret=PL_get_pointer(arg1,(void **)&env);
  RETURN_IF_FAIL
  ret=PL_get_pointer(arg2,(void **)&node);
  RETURN_IF_FAIL
  out=PL_new_term_ref();

  if (!Cudd_IsConstant(node))
  {
    table=init_table(env->boolVars);
    // dump_env(env);
    prob=Prob(node,env,table);
    if (Cudd_IsComplement(node))
      prob=1.0-prob;
    ret=PL_put_float(out,prob);
    RETURN_IF_FAIL
    destroy_table(table,env->boolVars);
  }
  else
  {
    if (node==Cudd_ReadOne(env->mgr))
    {
      ret=PL_put_float(out,1.0);
      RETURN_IF_FAIL
    }
    else
    {
      ret=PL_put_float(out,0.0);
      RETURN_IF_FAIL
    }
  }

  return(PL_unify(out,arg3));
}

// void print_paths_table(all_paths_table *a_p_t) {
//   int i,j,k;
//   for(i = 0; i < a_p_t->n_elements; i++) {
//     printf("Index: %d, n paths: %d\n",i,a_p_t->pt[i].n_paths);
//     for(j = 0; j < a_p_t->pt[i].n_paths; j++) {
//       printf("\tPath: %d, n_nodes = %d, prob: %lf\n", j, a_p_t->pt[i].paths_list[j].n_nodes, a_p_t->pt[i].paths_list[j].prob);
//       printf("\t\t[");
//       for(k = 0; k < a_p_t->pt[i].paths_list[j].n_nodes; k++) {
//         printf("%s%d ",a_p_t->pt[i].paths_list[j].nodes[k].mode == 1 ? "" : "not ",a_p_t->pt[i].paths_list[j].nodes[k].index);
//       }
//       printf("]\n");
//     }
//   }
// }

// 1 0 -> [1-1,0,1]
// 3 2 not 1 0 -> [3-1,2-1,1-0,0-1]
// 3 2 not 0 -> [3-1,2-1,0-0]
// generates only the paths
term_t generate_prolog_paths_list(paths_table *table) {
  int i, j, ret;
  term_t out, out_in, var, val, head;
  functor_t minus;
  minus=PL_new_functor(PL_new_atom("-"), 2);
  out = PL_new_term_ref();
  head = PL_new_term_ref();

  PL_put_nil(out);

  for(i = 0; i < table->n_paths; i++) {
    out_in = PL_new_term_ref();
    PL_put_nil(out_in);

    for(j = 0; j < table->paths_list[i].n_nodes; j++) {
      var = PL_new_term_ref();
      val = PL_new_term_ref();
      
      ret = PL_put_integer(var,table->paths_list[i].nodes[j].index);
      RETURN_IF_FAIL
      
      ret = PL_put_integer(val,table->paths_list[i].nodes[j].mode);
      RETURN_IF_FAIL
      
      ret=PL_cons_functor(head, minus,var,val);
      RETURN_IF_FAIL

      ret = PL_cons_list(out_in,head,out_in);
      RETURN_IF_FAIL
    }

    ret = PL_cons_list(out,out_in,out);
    RETURN_IF_FAIL
  }

  return out;
}

// generates only the probs
// term_t generate_prolog_prob_paths_list(paths_table *table) {
//   int i, ret;
//   term_t out;
//   term_t number;
//   out = PL_new_term_ref();
//   number = PL_new_term_ref();

//   PL_put_nil(out);
//   for(i = 0; i < table->n_paths; i++) {
//     ret = PL_put_float(number,table->paths_list[i].prob);
//     RETURN_IF_FAIL

//     ret = PL_cons_list(out,number,out);
//     RETURN_IF_FAIL
//   }

//   return out;
// }

void populate_influence_list(environment *env, inf_tab *influence_tab, paths_table *pt) {
  // loop thorugh all the paths
  // compute all the probs
  int i, j, k;
  for(i = 0; i < pt->n_paths; i++) {
    for(j = 0; j < pt->paths_list[i].n_nodes; j++) {
      for(k = 0; k < influence_tab->n_values; k++) {
        influence_tab->tab[k].prob_f = 1;
        influence_tab->tab[k].prob_tr = 1; 
      }
      for(k = 0; k < influence_tab->n_values; k++) {
        if(k == j) {
          if(pt->paths_list[i].nodes[j].mode == 0) {
            influence_tab->tab[k].prob_f = 1;
          }
          else {
            influence_tab->tab[k].prob_tr = 1;
          }
        }
        else {
          influence_tab->tab[k].p_ev_true *= env->probs[pt->paths_list[i].nodes[j].index];
          influence_tab->tab[k].p_ev_false *= env->probs[pt->paths_list[i].nodes[j].index];
        }
      }
      
      influence_tab->tab[k].p_ev_true += influence_tab->tab[k].prob_tr;
      influence_tab->tab[k].p_ev_false += influence_tab->tab[k].prob_f;
    }
  }

}


static foreign_t ret_influence_prob(term_t env_ref, term_t root, term_t prob_out, term_t influence_table_ref) {
  term_t out, influence_table;
  environment * env;
  DdNode * node;
  tablerow * table;
  double prob = 0;
  int ret, i;
  inf_tab influence_list;
  // all_paths_table a_p_t;

  ret=PL_get_pointer(env_ref,(void **)&env);
  RETURN_IF_FAIL
  ret=PL_get_pointer(root,(void **)&node);
  RETURN_IF_FAIL
  out=PL_new_term_ref();
  influence_table = PL_new_term_ref();

  if (!Cudd_IsConstant(node)) {
    table=init_table(env->boolVars);

    Cudd_PrintMinterm(env->mgr,node);

    // a_p_t.n_elements = env->boolVars;
    // for(i = 0; i < env->boolVars; i++) {
    //   a_p_t.pt[i].n_paths = 0;
    // }

    // init influence table: one element for each node
    influence_list.tab = malloc(sizeof(infl_table) * (Cudd_ReadSize(env->mgr)));
    for(i = 0; i < Cudd_ReadSize(env->mgr); i++) {
      influence_list.tab[i].p_ev_true = 1.0;
      influence_list.tab[i].p_ev_false = 1.0;
    }
    influence_list.n_values = Cudd_ReadSize(env->mgr);

    // prob = Prob_influence(node,env,table,influence_list);
    // if (Cudd_IsComplement(node)) {
    //   prob=1.0-prob;
    // }
    // prob = Prob_paths(node, env, table, &a_p_t, Cudd_NodeReadIndex(node));
    if (Cudd_IsComplement(node)) {
      prob=1.0-prob;
    }

    // popolate_influence_list(env,&influence_list,&a_p_t.pt[Cudd_NodeReadIndex(node)]);

    for(i = 0; i < Cudd_ReadSize(env->mgr); i++) {
      printf("%d - ev_true: %lf, ev_false: %lf\n",i,influence_list.tab[i].p_ev_true, influence_list.tab[i].p_ev_false);
    }

    ret=PL_put_float(out,prob);
    RETURN_IF_FAIL
    destroy_table(table,env->boolVars);
  }
  else {
    if (node==Cudd_ReadOne(env->mgr)) {
      ret=PL_put_float(out,1.0);
      RETURN_IF_FAIL
    }
    else {
      ret=PL_put_float(out,0.0);
      RETURN_IF_FAIL
    }
  }

  return(PL_unify(out,prob_out) && PL_unify(influence_table,influence_table_ref));
}

// converts a list of path (0,1) into an equation
// of the form x+y...
char *from_paths_to_sym_eq(paths_table *table, environment *env, all_data *opt_data, int *malloc_size) {
  int i, j, k, index, mode;
  char *result = malloc(1);

  int size = 1;
  result[0] = '\0';
 
  // dump_env(env);
  // printf("n paths: %d\n",table->n_paths);
  for(i = 0; i < table->n_paths; i++) {
    // printf("current: %d\n",i);
    // printf("table->paths_list[i].n_nodes %d\n",table->paths_list[i].n_nodes);
    for(j = 0; j < table->paths_list[i].n_nodes; j++) {
      index = table->paths_list[i].nodes[j].index;
      mode = table->paths_list[i].nodes[j].mode;
      // printf("index %d - %d\n",index,env->nVars);
      if(env->vars[index].optimize == 1) {
        // extract name
        for(k = 0; k < opt_data->n_triples; k++) {
          // printf("opt_data->triple[k].index_bdd %d \n",opt_data->triple[k].index_bdd);
          if(opt_data->triple[k].index_bdd == env->vars[index].nRule) {
            // extract the name
            if(mode == 0) {
              size = size + strlen(opt_data->triple[k].name) + 5; // 5 is (1-)*
              result = realloc(result, size); 
              snprintf(result + strlen(result), size, "(1-%s)*",opt_data->triple[k].name);
              // printf("(1 - %s)*",opt_data->triple[k].name);
            }
            else {
              size = size + strlen(opt_data->triple[k].name) + 1;
              result = realloc(result, size); // 1 is *
              snprintf(result + strlen(result), size, "%s*",opt_data->triple[k].name);
              // printf("%s*",opt_data->triple[k].name);
            }
            break;
          }
        }
      }
      else {
        // printf("prob\n");
        // extract prob env->probs[index];
        size = size + 7;
        result = realloc(result, size); // 6 is 0.4lf
        snprintf(result + strlen(result), size, "%.4lf*", mode == 1 ? env->probs[index] : 1 - env->probs[index]);
      }
    }
    size = size + 7;
    result = realloc(result, size);
    snprintf(result + strlen(result), size, "%.4lf+", table->paths_list[i].prob);
  }

  result[strlen(result) - 1] = '\0'; // eat the extra +
  *malloc_size = size;
  return result;
}

// i cannot use the current constraint index, need to pass the costraint one
double constraint_func(unsigned n, const double *x, double *grad, void *data) {
  char *map = malloc(2);
  int map_size = 3;
  int i,j, pos = -1;
  double retval;

  all_data *my_func_data = (all_data *)data;
  assert(my_func_data->current_constraint != NULL && "in constraint_func");
  // printf("my_func_data->current_constraint: %s\n",my_func_data->current_constraint);

  map[0] = '[';
  map[1] = '\0';
  // printf("my_func_data->n_triples %d\n",my_func_data->n_triples);
  for(i = 0; i < my_func_data->n_triples; i++) {
    // printf("x[my_func_data->triple[%d].index_array] , my_func_data->triple[].index_array = %d,  = %lf\n",i,my_func_data->triple[i].index_array,x[my_func_data->triple[i].index_array]);
    assert(my_func_data->triple[i].index_array < n);
    // printf("%d\n",my_func_data->triple[i].index_array);
    if (strstr(my_func_data->current_constraint, my_func_data->triple[i].name) != NULL) {
      map_size = map_size + strlen(my_func_data->triple[i].name) + 6 + 4; // should be + 2, +4 just to be sure
      map = realloc(map,map_size);
      snprintf(map + strlen(map), map_size, "[%s,%.4lf],", my_func_data->triple[i].name, x[my_func_data->triple[i].index_array]);
    }
    // printf("%s\n",map);
  }
  map_size = map_size + 2;
  map = realloc(map,map_size);
  map[strlen(map) - 1] = ']';
  map[strlen(map)] = '\0';

  // snprintf(map, 1024, "[[r,%lf],[g,%lf]]", x[0], x[1]); // <---------

  for (i = 0; i < strlen(map); i++) {
    if ((map[i] == '0' || map[i] == '1') && map[i + 1] == ',') {
      map[i + 1] = '.';
      i++;
    }
  }

  // printf("%s\n",map);


  if(grad) {
    for(i = 0; i < n; i++) {
      pos = -1;

      for(j = 0; j < my_func_data->n_triples && (pos == -1); j++) {
        // printf("Index. %d\n",my_func_data->triple[j].index_array);
        if(my_func_data->triple[j].index_array == i) {
          pos = j;
        }
      }

      // printf("Pos: %d, my_func_data->n_triples: %d, n: %d\n",pos,my_func_data->n_triples,n);
      assert(pos >= 0 && pos < my_func_data->n_triples && "pos >= 0");

      // printf("evaluate_derivative: %s in %s\n", my_func_data->current_constraint, my_func_data->triple[pos].name);
      // to speed up: if is not substring then avoid the prolog call 
      if (strstr(my_func_data->current_constraint, my_func_data->triple[pos].name) != NULL) {
        grad[i] = evaluate_or_derivate_function("evaluate_derivative",4,my_func_data->current_constraint, map, my_func_data->triple[pos].name);
      }
      else {
        // printf("evaluate_derivative: %s in %s\n", my_func_data->current_constraint, my_func_data->triple[pos].name);
        // printf("Gradient 0\n");
        grad[i] = 0;
      }

      // printf("pos: %d - name: %s - grad[%d] = %lf\n", pos, my_func_data->triple[pos].name, i, grad[i]);
    }      
  }

  // printf("evaluate: %s in %s\n",my_func_data->current_constraint,map);
  retval = evaluate_or_derivate_function("evaluate_expr",3,my_func_data->current_constraint, map, NULL);
  
  // printf("ret: %lf\n",retval);
  free(map);

  return retval;
}

void init_pl() {
  char **av = (char **)malloc(sizeof(char *) * (3));
  int ac = 0;
  char av0[10] = "./";
  char av1[10] = "-q";          // quiet
  char av2[15] = "--nosignals"; // signal handling

  av[ac++] = av0;
  av[ac++] = av1;
  av[ac++] = av2;

  if (!PL_is_initialised(NULL, NULL)) {
    assert(PL_initialise(ac, av) && "PL_initialise failure");
  }
  
  free(av);
}

void end_pl() {
  if (PL_is_initialised(NULL, NULL)) {
    PL_cleanup(1);
  }

}

double evaluate_or_derivate_function(const char *predicate, int arity, char *function, char *variables, char *variable_d)
{
  // predicate = evaluate -> computes the derivative and evaluate
  // predicate = evaluate_expr -> evaluates the expression 
  term_t tq;
  
  predicate_t p_consult = PL_predicate("consult", 1, "database");
  term_t t = PL_new_term_ref();
  assert(PL_put_string_chars(t, differentiate_path) && "PL_put_string_chars");
  assert(PL_call_predicate(NULL, 0, p_consult, t) && "PL_call predicate");
  predicate_t p_query = PL_predicate(predicate, arity, "differentiate");

  assert(PL_is_initialised(NULL, NULL));

  if (variable_d == NULL) {
    tq = PL_new_term_refs(3);
  }
  else {
    tq = PL_new_term_refs(4);
  }

  assert(PL_put_string_chars(tq, function) && "PL_put_string_chars function failure");
  assert(PL_put_string_chars(tq + 1, variables) && "PL_put_string_chars variables failure");
  assert(PL_put_variable(tq + 2) && "PL_put_variable failure");

  if(variable_d != NULL) {
    assert(PL_put_string_chars(tq + 3, variable_d) && "PL_put_string_chars variable failure");
  }

  // PL_call_predicate(NULL,0,p_query,t);
  qid_t query = PL_open_query(NULL, PL_Q_NORMAL, p_query, tq);

  int result = PL_next_solution(query);
  // printf("query: %d result %d\n",query,result);
  double value_computed;
  if (result)
  {
    assert(PL_get_float(tq + 2, &value_computed) && "PL_get_float error");
    // printf("Found solution %f.\n", value_computed);
  }
  else
  {
    return -1;
  }
  PL_close_query(query);

  return value_computed;
}

void print_paths_table(paths_table paths_tab) {
  printf("-- PATHS TABLE --\n");
  int i, k;
  printf("paths_tab.n_paths: %d\n",paths_tab.n_paths);
  for (i = 0; i < paths_tab.n_paths; i++) {
    printf("%i: n_nodes: %d, prob: %lf\n - ",i, paths_tab.paths_list[i].n_nodes,paths_tab.paths_list[i].prob);
    for (k = 0; k < paths_tab.paths_list[i].n_nodes; k++) {
      printf("%s%d ", paths_tab.paths_list[i].nodes[k].mode == 1 ? "" : "not ", paths_tab.paths_list[i].nodes[k].index);
    }
    printf("\n");
  }
  printf("-- END PATHS TABLE --\n");
}

void from_file_to_paths(environment *env, FILE *fp, paths_table *paths_tab, int *index_in_path, int *n_index) {
  char ch = '_', prev_ch = '_';
  int index = 0; // line
  int var_number = 0;
  int found = 0;
  int i;
  // int n_vars = paths_tab.n_vars;
  // read the file
  /* 
  101-1 1
  1101- 1
  11101 1
  1111- 1
  */
  // and returns a list of paths of the form 
  // index = 4, mode = 1
  // index = 3, mode = 0
  while (!feof(fp)) {
    prev_ch = ch;
    ch = fgetc(fp);
    if (ch == '\n') {
      // printf("index: %d \n",index);
      index++;
      var_number = 0;
    }
    else if ((ch == '1' || ch == '0') && prev_ch != ' ') {
      // printf("%d ", n_vars - 1 - var_number);
      // paths_list[index].n_nodes++;
      // paths_list[index].nodes = realloc(paths_list[index].nodes, sizeof(couple) * paths_list[index].n_nodes);

      // paths_tab.paths_list[index].nodes[paths_tab.paths_list[index].n_nodes].index = n_vars - 1 - var_number;
      paths_tab->paths_list[index].nodes[paths_tab->paths_list[index].n_nodes].index = var_number;
      
      assert(env->nVars >= var_number);

      // if the opt variable is in the path add it to the list
      // if it is not already present  
      found = 0;
      if(env->vars[var_number].optimize == 1) {
        for(i = 0; i < *n_index && found == 0; i++) {
          if(index_in_path[i] == var_number) {
            found = 1; 
          }
        }
        if(found == 0) {
          index_in_path[*n_index] = var_number;
          (*n_index)++;
        }
      }

      if (ch == '1') {
          paths_tab->paths_list[index].nodes[paths_tab->paths_list[index].n_nodes].mode = 1;
      }
      else {
          paths_tab->paths_list[index].nodes[paths_tab->paths_list[index].n_nodes].mode = 0;
      }
      paths_tab->paths_list[index].n_nodes++;
      var_number++;
    }
    else if (ch == '-' && prev_ch != ' ') {
      // printf("%d ", n_vars - 1 - var_number);
      var_number++;
    }
  }
}

int is_number(char *s) {
  int i;
  if(s[0] == '0' && s[1] == '.') {
    for(i = 2; i < strlen(s); i++) {
      if(!isdigit(s[i])) {
        return -1;
      }
    }
    return 1;
  }
  return -1;
}

paths_table get_paths_rec(environment *env, DdNode *node, int comp_par, computed_paths_table *cpt, tablerow *table) {
  // DdNode *node = Cudd_Regular(n);
  DdNode *T, *F;
  paths_table computed_path;
  paths_table computed_true, computed_false;
  int i,j,comp;
  double p1;

  comp = Cudd_IsComplement(node);
  comp=(comp && !comp_par) ||(!comp && comp_par);

  computed_path.n_paths = 0;
  // computed_path.paths_list = NULL;

  if(Cudd_IsConstant(node)) {
    // printf("constant\n");
    computed_path.n_paths = 1;
    computed_path.paths_list = malloc(sizeof(path));
    if(comp) {
      computed_path.paths_list[0].prob = 0;
    }
    else {
      computed_path.paths_list[0].prob = 1;
    }
    // computed_path.paths_list[0].nodes = NULL; 
    computed_path.paths_list[0].n_nodes = 0; 
  }
  else if (Cudd_ReadPerm(env->mgr,Cudd_NodeReadIndex(node)) >= env->n_abd_boolVars) {
    // abd and opt have the same value
    p1 = Prob(node,env,table);
    if (comp)
      p1 = 1.0 - p1;
    // printf("Prob: %lf\n",p1);

    computed_path.n_paths = 1;
    computed_path.paths_list = malloc(sizeof(path));
    computed_path.paths_list[0].prob = p1;
    computed_path.paths_list[0].n_nodes = 0;
  }
  else {
    // check if the path is in the table
    // if(cpt->tables[Cudd_NodeReadIndex(node)].n_paths > 0 && cpt->tables[Cudd_NodeReadIndex(node)].comp == comp) {
    //   printf("Found\n");
    //   return cpt->tables[Cudd_NodeReadIndex(node)];
    // } 

    T = Cudd_T(node);
    F = Cudd_E(node);

    if(Cudd_IsComplement(node)) {
      T = Cudd_Not(T);
      F = Cudd_Not(F);
    }

    computed_true = get_paths_rec(env,T,comp,cpt,table);
    computed_false = get_paths_rec(env, F, comp, cpt,table);

    // printf("True\n");
    // print_paths_table(computed_true);
    // printf("False\n");
    // print_paths_table(computed_false);

    // printf("computed_true.n_paths: %d\n",computed_true.n_paths);
    computed_path.paths_list = malloc(sizeof(path)*(computed_true.n_paths));

    // computed_path.paths_list[0].n_nodes = 0;
    // computed_path.paths_list[0].nodes = NULL;
    for(i = 0; i < computed_true.n_paths; i++) {
      if(computed_true.paths_list[i].prob != 0) {
        // copy all the paths in the current list and add the current
        // with mode 1
        // printf("true: computed_true.paths_list[i].n_nodes: %d, computed_true.n_paths: %d\n",computed_true.paths_list[i].n_nodes,computed_true.n_paths);
        // computed_path.paths_list[i].nodes = malloc(sizeof(couple) * (computed_true.paths_list[i].n_nodes + 1)); // for the current node
        computed_path.paths_list[i].nodes = malloc(sizeof(couple) * Cudd_ReadSize(env->mgr)); // quick
        for(j = 0; j < computed_true.paths_list[i].n_nodes; j++) {
          // printf("copy\n");
          computed_path.paths_list[i].nodes[j].index = computed_true.paths_list[i].nodes[j].index;
          computed_path.paths_list[i].nodes[j].mode = computed_true.paths_list[i].nodes[j].mode;
        }
        // add current node
        
        // printf("i: %d\n",i);
        // computed_path.paths_list[i].nodes = realloc(computed_path.paths_list[i].nodes,sizeof(couple)*(j+1));
        computed_path.paths_list[i].nodes[j].index = Cudd_NodeReadIndex(node);
        computed_path.paths_list[i].nodes[j].mode = 1;

        computed_path.paths_list[i].n_nodes = j + 1;
        // double p = env->probs[Cudd_NodeReadIndex(node)];
        computed_path.paths_list[i].prob = computed_true.paths_list[i].prob;

        computed_path.n_paths++;
      }
    }

    // do the same for else
    computed_path.paths_list = realloc(computed_path.paths_list,sizeof(path)*(computed_false.n_paths + computed_true.n_paths));
    for(i = 0; i < computed_false.n_paths; i++) {
      if(computed_false.paths_list[i].prob != 0) {
        // copy all the paths in the current list and add the current
        // with mode 0
        // printf("false: %d\n",computed_false.n_paths);

        // computed_path.paths_list[computed_path.n_paths - 1].nodes = malloc(sizeof(couple) * (computed_false.paths_list[i].n_nodes + 1));
        computed_path.paths_list[computed_path.n_paths].nodes = malloc(sizeof(couple) * Cudd_ReadSize(env->mgr));
        for(j = 0; j < computed_false.paths_list[i].n_nodes; j++) {
          // copio tutti i nodi
          computed_path.paths_list[computed_path.n_paths].nodes[j].index = computed_false.paths_list[i].nodes[j].index;
          computed_path.paths_list[computed_path.n_paths].nodes[j].mode = computed_false.paths_list[i].nodes[j].mode;
        }
        // add current node
        // computed_path.paths_list[computed_path.n_paths - 1].nodes = realloc(computed_path.paths_list[computed_path.n_paths - 1].nodes, sizeof(couple) * (j + 1));
        computed_path.paths_list[computed_path.n_paths].nodes[j].index = Cudd_NodeReadIndex(node);
        computed_path.paths_list[computed_path.n_paths].nodes[j].mode = 0;

        computed_path.paths_list[computed_path.n_paths].n_nodes = j + 1;
        computed_path.paths_list[computed_path.n_paths].prob = computed_false.paths_list[i].prob;

        computed_path.n_paths++;
      }
    }
    // printf("computed_path.n_paths: %d\n", computed_path.n_paths);
  }

    // add the path to the table
    computed_path.comp = comp;
    if(!Cudd_IsConstant(node)) {
      cpt->tables[Cudd_NodeReadIndex(node)] = computed_path;
    }
  

  // printf("computed_path.n_paths: %d\n",computed_path.n_paths);

  return computed_path;
}



paths_table retrieve_paths_from_bdd(environment *env, DdNode *root) {
  int i;
  paths_table all_paths_list;
  computed_paths_table cpt; // to store already computed paths
  tablerow * table;

  cpt.n_nodes = Cudd_ReadSize(env->mgr);
  cpt.tables = malloc(sizeof(paths_table) * cpt.n_nodes);

  for(i = 0; i < cpt.n_nodes; i++) {
    cpt.tables[i].n_paths = -1;
    cpt.tables[i].n_vars = -1;
    cpt.tables[i].paths_list = NULL;
  }

  table = init_table(env->boolVars); // maybe env size?

  // printf("caller constant: %d\n",Cudd_IsConstant(root));
  all_paths_list = get_paths_rec(env,root,0,&cpt,table);

  destroy_table(table,env->boolVars);
  free(cpt.tables);

  return all_paths_list;
}

/*
// static foreign_t ret_prob_constr(term_t env_ref, term_t root, term_t objective, term_t mode, term_t constraintsList, InitValues,LIndexName, term_t assigments);
static foreign_t ret_opt_prob(term_t env_ref, term_t root, term_t objective, term_t goal_atom, term_t constraintsList, term_t bounds, term_t index_name, term_t algorithm, term_t max_exec_time, term_t assigments) {
  term_t out, obj_list, constr_list, bounds_list, head, head2, index_names_list;
  environment * env;
  DdNode * node;
  tablerow * table;
  double prob, optimal_value = -1;
  int i,j,k,l,m,n, ret; 
  int alg_index,exec_time;

  double *variables_to_optimize;
  size_t len_constr_list, n_opt_vars = 0;
  // int ret, i, j, k;
  // paths_table paths_tab;
  // char objective_func[MAP_SIZE];
  char *objective_func;
  size_t len_obj;
  char **constraints;
  char goal_a[MAP_SIZE]; // this can be in stack
  char *symbolic_path;
  // char current_constr[64];
  size_t len_constr, n_index_names;
  paths_table pt_test;

  nlopt_opt opt; // algorithm data structure
  all_data opt_data; // needed to find pairs
  all_data *array_list;

  int found = 1;
  char temp_string[256];
  char *temp_string_1 = NULL;
  char *temp_string_2 = NULL;

  char *map; 
  int map_size = 0;

  nlopt_result res;

  clock_t begin;
  clock_t end;
  int malloc_size = 0;
  double time_spent = 0;

  char *str_tmp;

  double *ub, *lb;

  FILE *fp_py;
  int size = 1;

  setlocale(LC_NUMERIC, "en_US.UTF-8"); // to have . instead of ,

  opt_data.n_constraints = 0;
  // opt_data.current_constraint = -1;

  head = PL_new_term_ref();
  head2 = PL_new_term_ref();
  out = PL_new_term_ref();

  assert(PL_get_pointer(env_ref,(void **)&env));
  assert(PL_get_pointer(root,(void **)&node));
  // assert(PL_get_integer(mode,&mode_type));
  
  assert(PL_get_integer(algorithm,&alg_index));
  assert(PL_get_integer(max_exec_time,&exec_time));

  obj_list = PL_copy_term_ref(objective);
  assert(PL_get_string_chars(obj_list,&temp_string_2,&len_obj));
  // snprintf(objective_func,MAP_SIZE,"%s",temp_string_2);  
  objective_func = malloc(len_obj + 2);
  snprintf(objective_func,len_obj + 1,"%s",temp_string_2);  
  for(k = 0; k < strlen(objective_func); k++) {
    if(objective_func[k] == '(' || objective_func[k] == ')' || objective_func[k] == ',') {
      objective_func[k] = '_';
    }
  }

  // printf("obj: %s len: %d\n",objective_func,(int)len_obj);
  // opt_data.to_optimize = malloc(100);
  opt_data.to_optimize = malloc(len_obj + 2);
  snprintf(opt_data.to_optimize, len_obj + 1, "%s", objective_func);
  // snprintf(opt_data.to_optimize,MAP_SIZE,"%s",objective_func);

  constr_list = PL_copy_term_ref(constraintsList);
  ret = PL_skip_list(constr_list,0,&len_constr_list);
  if (ret != PL_LIST) 
    return FALSE;  
  
  // printf("Len constr_list: %d\n",(int)len_constr_list);
  constraints = (char **)malloc(len_constr_list * sizeof(char*));
  opt_data.constraints = (char **)malloc(len_constr_list * sizeof(char*));
  opt_data.n_constraints = 0;

  for(i = 0; i < len_constr_list; i++) {
    assert(PL_get_list(constr_list, head, constr_list));
    assert(PL_get_string_chars(head,&constraints[i],&len_constr));
    opt_data.constraints[opt_data.n_constraints] = malloc(1024);

    snprintf(opt_data.constraints[opt_data.n_constraints],1024,"%s",constraints[i]);
    for(k = 0; k < strlen(opt_data.constraints[opt_data.n_constraints]); k++) {
      if(opt_data.constraints[opt_data.n_constraints][k] == '(' || opt_data.constraints[opt_data.n_constraints][k] == ')' || opt_data.constraints[opt_data.n_constraints][k] == ',') {
        opt_data.constraints[opt_data.n_constraints][k] = '_';
      }
    }
    opt_data.n_constraints++;
  }

  bounds_list = PL_copy_term_ref(bounds);
  assert(PL_skip_list(bounds_list,0,&n_opt_vars) && "PL_skip_list bounds_list error");

  index_names_list = PL_copy_term_ref(index_name);
  assert(PL_skip_list(index_names_list,0,&n_index_names) && "PL_skip_list index_names_list error");

  opt_data.triple = malloc(sizeof(name_indexes) * n_opt_vars);
  opt_data.n_triples = n_opt_vars;

  array_list = malloc((len_constr_list + 1)*sizeof(all_data)); // +1 for objective
  for(i = 0; i <= len_constr_list; i++) {
    array_list[i].constraints = opt_data.constraints;
    array_list[i].n_constraints = opt_data.n_constraints;
    array_list[i].n_triples = opt_data.n_triples;
    array_list[i].triple = opt_data.triple;
  }
  //
  // char **ts = malloc(sizeof(char **) * n_index_names);

  for(i = 0; i < n_index_names; i++) {
    assert(PL_get_list(index_names_list, head, index_names_list));
    // read index and name
    assert(PL_get_list(head,head2,head));
    assert(PL_get_integer(head2,&opt_data.triple[i].index_bdd));
    opt_data.triple[i].index_array = i;

    assert(PL_get_list(head,head2,head));
    assert(PL_get_string_chars(head2, &str_tmp, &len_obj));
    snprintf(opt_data.triple[i].name,MAP_SIZE,"%s",str_tmp);
    for(k = 0; k < strlen(opt_data.triple[i].name); k++) {
      if(opt_data.triple[i].name[k] == '(' || opt_data.triple[i].name[k] == ')' || opt_data.triple[i].name[k] == ',') {
        opt_data.triple[i].name[k] = '_';
      }
    }
  }

  // dump_env(env);

  // reordering to have optimizable vars at the beginning
  assert(reorder_int(env));

  // for(i = 0; i < n_index_names; i++) {
  //   opt_data.triple[i].index_bdd = Cudd_ReadPerm(env->mgr,opt_data.triple[i].index_bdd);
  // }
  // printf("Opt data:\n");
  // for (i = 0; i < n_opt_vars; i++)
  // {
  //   printf("bdd: %d arr: %d name: %s\n", opt_data.triple[i].index_bdd, opt_data.triple[i].index_array, opt_data.triple[i].name);
  // }

  if (!Cudd_IsConstant(node)) {
    table=init_table(env->boolVars);

    begin = clock();

    pt_test = retrieve_paths_from_bdd(env,node);
    // print_paths_table(pt_test);
    symbolic_path = from_paths_to_sym_eq(&pt_test,env,&opt_data,&malloc_size);
    // printf("symbolic_path: %s\n",symbolic_path);
    // printf("sym path malloc size: %d\n",malloc_size);

    
    // generate the command
    char *symbols = malloc(1);
    symbols[0] = '\0';

    for(k = 0; k < opt_data.n_triples; k++) {
      size = size + strlen(opt_data.triple[k].name) + 2;
      symbols = realloc(symbols, size); 
      snprintf(symbols + strlen(symbols), size, "%s,",opt_data.triple[k].name);
    }
    symbols[strlen(symbols) - 1] = '\0';

    char *temp_res = malloc(strlen(symbols) + 2);
    strcpy(temp_res,symbols);

    // make space for the command
    size = size + size + 30;
    symbols = realloc(symbols, size);
    // ebd, ebc = symbols('ebd ebc')
    snprintf(symbols, size, "%s = symbols(\'%s\')",temp_res, temp_res);

    free(temp_res);

    // printf("symbols: %s\n",symbols);
    // exit(-1);
    // char *command = "print(simplify(ebd*ebc*0.774 + (1- ebd)*ebc*0.27 + ebd*(1-ebc)*0.72))";
    char *command = malloc(strlen(symbolic_path) + 25);
    // snprintf(command,strlen(symbolic_path) + 20,"print(simplify(%s))",symbolic_path);
    snprintf(command,strlen(symbolic_path) + 20,"a = simplify(%s)",symbolic_path);
    
    // printf("command: %s\n",command);
    
    // exit(-1);

    // Open the command for reading.
    // char *symbols = "ebd, ebc = symbols('ebd ebc')";
    // char *command = "print(simplify(ebd*ebc*0.774 + (1- ebd)*ebc*0.27 + ebd*(1-ebc)*0.72))";
    char exec_this[10000]; // maximum length
    char *obtained_from_py = NULL;
    size_t lenline;
    // check to avoid overflow, also to avoid a too long computation in the simplification
    if(strlen(py_path) + strlen(symbols) + strlen(command) < 10000) {      
      snprintf(exec_this, 10000, "%s \"%s\" \"%s\"", py_path, symbols, command);
      fp_py = popen(exec_this, "r");
      if (fp_py == NULL) {
        printf("Failed to run command\n" );
        PL_fail;
      }

      if(getline(&obtained_from_py, &lenline, fp_py) < 0) {
        printf("error while calling python");
        PL_fail;
      }
      // printf("Obtained: %s\n", obtained_from_py);
      pclose(fp_py);
      free(symbolic_path);
      symbolic_path = obtained_from_py;
    }

    free(command);
    free(symbols);

    end = clock();
    time_spent = (double)(end - begin) / CLOCKS_PER_SEC;
    // printf("BDD: %lf\n",time_spent);

    // if symbolic path is a number handle it!
    if(is_number(symbolic_path) < 0) {

      assert(PL_get_string_chars(goal_atom, &temp_string_1, &len_obj) && "PL_get_atom_chars(goal_atom,goal_a) failure");
      snprintf(goal_a,MAP_SIZE,"%s",temp_string_1);
      for(k = 0; k < strlen(goal_a); k++) {
        if(goal_a[k] == '(' || goal_a[k] == ')' || goal_a[k] == ',') {
          goal_a[k] = '_';
        }
      }

      // printf("pre loop: goal_a: %s\n",goal_a);
      // this super loop is needed to replace the name of the goal
      // with its path representation
      for(i = 0; i < len_constr_list; i++) {
        for(j = 0; j < strlen(opt_data.constraints[i]); j++) {
          if(opt_data.constraints[i][j] == goal_a[0]) {
            for(k = 0; k < strlen(goal_a) && k < strlen(opt_data.constraints[i]); k++) {
              if (opt_data.constraints[i][j + k] != goal_a[k]) {
                // printf("opt_data.constraints[i][j + k] = %c - result[k] = %c\n",opt_data.constraints[i][j + k], result[k]);
                found = 0;
                break;
              }
            }
            if(found == 1) {
              // printf("found\n");
              opt_data.constraints[i] = realloc(opt_data.constraints[i], 1024 + strlen(symbolic_path));
              // printf("-> %c\n",opt_data.constraints[i][j+k]);
              if (opt_data.constraints[i][j + k] == '-' || opt_data.constraints[i][j + k] == '+' || opt_data.constraints[i][j + k] == ' ' || opt_data.constraints[i][j + k] == '*' || opt_data.constraints[i][j + k] == '/' || opt_data.constraints[i][j + k] == '\0')
              {
                // printf("ok\n");
                snprintf(temp_string,256,"%s",opt_data.constraints[i]);
                // opt_data.constraints[i][j + k - 1] = '(';
                opt_data.constraints[i][j] = '(';
                // for(l = k; l < strlen(symbolic_path) + 1; l++) {
                for(l = j + 1; l < strlen(symbolic_path) + j + 1; l++) {
                  // opt_data.constraints[i][j+l] = symbolic_path[l-1];
                  opt_data.constraints[i][l] = symbolic_path[l-j-1];
                  // printf("%c\n",opt_data.constraints[i][j+l]);
                }
                // opt_data.constraints[i][j+l] = ')';
                opt_data.constraints[i][l] = ')';
                n = 1;
                for (m = j + k; m < strlen(temp_string); m++) {
                  opt_data.constraints[i][j+l+n] = temp_string[m];
                  n++;
                }
                // opt_data.constraints[i][j+l+n] = '\0';
                opt_data.constraints[i][l + m + 1 - j - k] = '\0';
              }
            }
          }
          found = 1;
        }
      }

      // printf("goal_a: %s\n",goal_a);
      // printf("--- opt_data.constraints[i]\n");
      // for(i = 0; i < len_constr_list; i++) {
      //   printf("%s\n",opt_data.constraints[i]);
      // }

      // PL_fail;

      ub = malloc(sizeof(double)*n_opt_vars);
      lb = malloc(sizeof(double)*n_opt_vars);
      variables_to_optimize = malloc(sizeof(double) * (int)n_opt_vars);

      for(i = 0; i < n_opt_vars; i++) {
        assert(PL_get_list(bounds_list, head, bounds_list)); // now head is [LB,UB]
        assert(PL_get_list(head, head2, head));      
        assert(PL_get_float(head2,&lb[i]));
        assert(PL_get_list(head, head2, head)); 
        assert(PL_get_float(head2,&ub[i]));
        variables_to_optimize[i] = lb[i] + (ub[i] - lb[i])/2 ;
      }

      // non linearity constraints are supported by only few algorithms
      switch (alg_index) {
      case 0:
        opt = nlopt_create(NLOPT_LD_MMA, n_opt_vars);
        break;
      case 1:
        opt = nlopt_create(NLOPT_LD_CCSAQ, n_opt_vars);
        break;
      case 2:
        opt = nlopt_create(NLOPT_LD_SLSQP, n_opt_vars);
        break;
      default:
        PL_fail;
        break;
      }
      // opt = nlopt_create(NLOPT_LD_SLSQP, n_opt_vars);

      nlopt_set_upper_bounds(opt, ub);
      nlopt_set_lower_bounds(opt, lb);
      
      // opt_data.current_constraint = -1; // to set objective
      // opt_data.current_constraint = opt_data.to_optimize;
      array_list[0].current_constraint = opt_data.to_optimize;
      nlopt_set_min_objective(opt, constraint_func, &array_list[0]);
      // nlopt_set_min_objective(opt, constraint_objective, &opt_data);
      
      if(exec_time > 0) {
        nlopt_set_maxtime(opt,(double)exec_time);
      }
    
      for(i = 0; i < len_constr_list; i++) {
        // set constraints from the user
        array_list[i + 1].current_constraint = opt_data.constraints[i]; 
        // opt_data.current_constraint = opt_data.constraints[i];
        // printf("-> %s\n",array_list[i + 1].current_constraint);
        nlopt_add_inequality_constraint(opt, constraint_func, &array_list[i + 1], 1e-5);
      }

      nlopt_set_xtol_rel(opt, 1e-5); // tolerance


      begin = clock();

      init_pl();
      res = nlopt_optimize(opt, variables_to_optimize, &optimal_value);
      // printf("nlopt result: %d\n",res);
      // const char code = nlopt_result_to_string(res);

      end = clock();
      time_spent = (double)(end - begin) / CLOCKS_PER_SEC;
      // printf("OPT time: %lf\n",time_spent);

      if (res < 0) {
        printf("nlopt failed!\n");
        // this means that the problem is not satisfiable
      }
      else {
        // printf("after %d evaluations, found minimum at f(",nlopt_get_numevals(opt));
        // for(i = 0; i < n_opt_vars; i++) {
        //   printf("%g,",variables_to_optimize[i]);
        // }
        // printf(") = %0.10g\n", optimal_value);
        free(lb);
        free(ub);

        map = malloc(2);
        map_size = 2;
        
        map[0] = '[';
        map[1] = '\0';
        for(i = 0; i < array_list[0].n_triples; i++) {
          // printf("x[my_func_data->triple[%d].index_array] , my_func_data->triple[].index_array = %d,  = %lf\n",i,my_func_data->triple[i].index_array,x[my_func_data->triple[i].index_array]);
          assert(array_list[0].triple[i].index_array < n_opt_vars);
          map_size = map_size + strlen(array_list[0].triple[i].name) + 6 + 4; // should be + 2, +4 just to be sure
          map = realloc(map,map_size);
          snprintf(map + strlen(map), map_size, "[%s,%.4lf],", array_list[0].triple[i].name, variables_to_optimize[array_list[0].triple[i].index_array]);
        }
        map_size = map_size + 2;
        map = realloc(map,map_size);
        
        map[strlen(map) - 1] = ']';
        map[strlen(map)] = '\0';

        prob = evaluate_or_derivate_function("evaluate_expr",3,symbolic_path, map, NULL);
        assert(prob >= 0 && prob <= 1);
        // printf("Prob: %lf map: %s\n",prob,map);

        // create list out
        assert(PL_put_nil(out));
        functor_t minus; 
        minus = PL_new_functor(PL_new_atom("-"), 2);
        term_t name_term = PL_new_term_ref();
        term_t prob_term = PL_new_term_ref();

        for(i = 0; i < array_list[0].n_triples; i++) {
          assert(PL_put_float(prob_term,variables_to_optimize[array_list[0].triple[i].index_array]));
          assert(PL_put_term_from_chars(name_term,0,strlen(array_list[0].triple[i].name),array_list[0].triple[i].name));
          head = PL_new_term_ref();
          assert(PL_cons_functor(head, minus, name_term, prob_term));
          assert(PL_cons_list(out, head, out));
        }

        // add ass-prob
        assert(PL_put_float(prob_term, prob));
        assert(PL_put_term_from_chars(name_term, 0, 1, "p"));
        head = PL_new_term_ref();
        assert(PL_cons_functor(head, minus, name_term, prob_term));
        assert(PL_cons_list(out, head, out));
      }

      free(variables_to_optimize);
    
      nlopt_destroy(opt);
      free(objective_func);
      // for(i = 0; i < len_constr_list; i++) {
      //   free(constraints[i]);
      // }
      free(constraints);
      free(opt_data.to_optimize);

      destroy_table(table,env->boolVars);
    }
    else {
      assert(PL_put_string_chars(out,symbolic_path));
    }
    // end_pl(); // <---- if you call it you will get a segfault

    if(obtained_from_py != NULL) {
      free(obtained_from_py);
    }
    
  }
  else {
    if (node==Cudd_ReadOne(env->mgr)) {
      ret=PL_put_float(out,1.0);
      RETURN_IF_FAIL
    }
    else {
      ret=PL_put_float(out,0.0);
      RETURN_IF_FAIL
    }
  }

  // assert(PL_put_float(out, optimal_value));
  return PL_unify(out, assigments);
}
*/



double Prob_influence(DdNode *node, environment *env, tablerow *table, infl_table *infl_t) {
  int index, i;
  double res;
  double p,pt,pf,BChild0,BChild1;
  double * value_p;
  DdNode *nodekey,*T,*F;
  if (Cudd_IsConstant(node)) {
    return 1.0;
  }
  else
  {
    nodekey=Cudd_Regular(node);
    value_p=get_value(table,nodekey);
    if (value_p!=NULL)
        return *value_p;
    else
    {
      index=Cudd_NodeReadIndex(node);  //Returns the index of the node. The node pointer can be either regular or complemented.
      //The index field holds the name of the variable that labels the node. The index of a variable is a permanent attribute that reflects the order of creation.
      p=env->probs[index];
      T = Cudd_T(node);
      F = Cudd_E(node);
      pf = Prob_influence(F,env,table,infl_t);
      pt = Prob_influence(T,env,table,infl_t);
      if (Cudd_IsComplement(F))
        pf=1.0-pf;

      infl_t[index].p_ev_true = pt;
      infl_t[index].p_ev_false = pf;

      BChild0=pf*(1-p);
      BChild1=pt*p;
      res=BChild0+BChild1;

      /**
       * per la probabilità dell'evidenza, devo considerare anche tutti
       * i percorsi che non passano per un nodo: se esistono dei percorsi
       * che non passano per un nodo allora la prob | nodo vero o falso
       * non cambia per quel ramo. Metto in standby
       *  
       * */

      for(i = 0; i < env->boolVars; i++) {
        if(i != index) {
          infl_t[i].p_ev_true = infl_t[i].p_ev_true * res;
          infl_t[i].p_ev_false = infl_t[i].p_ev_false * res;
        }
        else {
          infl_t[i].p_ev_true = pt;
          infl_t[i].p_ev_false = pf;
        }
      }

      add_node(table,nodekey,res);
      return res;
    }
  }
}

int reorder_int(environment *env)
{
  int i,j,var_ind,abd_ind=0,ind=env->n_abd_boolVars;
  variable var,* vars=env->vars;
  DdManager *mgr=env->mgr;
  // int boolVars=env->boolVars;
  int * permutation;
  int * bVar2mVar=env->bVar2mVar;

  // permutation=malloc((boolVars)*sizeof(int));
  permutation = malloc((Cudd_ReadSize(env->mgr))*sizeof(int));

  for (i=0;i<Cudd_ReadSize(env->mgr);i++)
  {
    j=Cudd_ReadInvPerm(mgr,i);
    var_ind=bVar2mVar[j];
    var=vars[var_ind];
    if (var.abducible || var.query || var.optimize)
    {
      permutation[abd_ind]=j;
      abd_ind++;
    }
    else
    {
      permutation[ind]=j;
      ind++;
    }

  }

  // for(i = 0; i < Cudd_ReadSize(env->mgr); i++) {
  //   printf("%d\n",permutation[i]);
  // }

  j = Cudd_ShuffleHeap(mgr,permutation);

  free(permutation);

  return j;
}

static foreign_t reorder(term_t arg1)
{
  environment * env;
  int ret;

  ret=PL_get_pointer(arg1,(void **)&env);
  RETURN_IF_FAIL
  ret=reorder_int(env);
  RETURN_IF_FAIL
  return 1;
}

static foreign_t ret_abd_prob(term_t arg1, term_t arg2,
  term_t arg3, term_t arg4)
{
  term_t out,outass;
  environment * env;
  DdNode * node;
  expltablerow * expltable;
  tablerow * table;
  //abdtablerow * abdtable;
  prob_abd_expl delta;
  int ret;
  double p;
  explan_t * mpa;
  // assign *array_mpa;


  ret=PL_get_pointer(arg1,(void **)&env);
  RETURN_IF_FAIL
  ret=PL_get_pointer(arg2,(void **)&node);
  RETURN_IF_FAIL
  out=PL_new_term_ref();

  ret=reorder_int(env);
  RETURN_IF_FAIL

  // array_mpa = malloc(sizeof(assign) * env->boolVars);

  if (!Cudd_IsConstant(node))
  {
    expltable=expl_init_table(env->boolVars);
    table=init_table(env->boolVars);
    //abdtable=init_abd_table(env->n_abd);

    delta=abd_Prob(node,env,expltable,table,0);
    p=delta.prob;
    mpa=delta.mpa;
    ret=PL_put_float(out,p);
    RETURN_IF_FAIL
    //destroy_table(abdtable,env->n_abd);
    outass=abd_clist_to_pllist(mpa);
    RETURN_IF_FAIL
    expl_destroy_table(expltable,env->boolVars);
    destroy_table(table,env->boolVars);
  }
  else
  {
    if (node==Cudd_ReadOne(env->mgr))
    {
      ret=PL_put_float(out,1.0);
      RETURN_IF_FAIL
    }
    else
    {
      ret=PL_put_float(out,0.0);
      RETURN_IF_FAIL
    }
      outass=PL_new_term_ref();
      ret=PL_put_nil(outass);
      RETURN_IF_FAIL
  }

  return(PL_unify(out,arg3)&&PL_unify(outass,arg4));
}

static foreign_t ret_map_prob(term_t arg1, term_t arg2,
  term_t arg3, term_t arg4)
{
  term_t out,outass;
  environment * env;
  DdNode * node;
  expltablerow * maptable;
  tablerow * table;
  //abdtablerow * abdtable;
  prob_abd_expl delta;
  int ret;
  double p;
  explan_t * mpa;

  ret=PL_get_pointer(arg1,(void **)&env);
  RETURN_IF_FAIL
  ret=PL_get_pointer(arg2,(void **)&node);
  RETURN_IF_FAIL
  out=PL_new_term_ref();

  ret=reorder_int(env);

  RETURN_IF_FAIL

  if (!Cudd_IsConstant(node))
  {
    maptable=expl_init_table(env->boolVars);
    table=init_table(env->boolVars);
    //abdtable=init_abd_table(env->n_abd);
    delta=map_Prob(node,env,maptable,table,0);
    p=delta.prob;
    mpa=delta.mpa;
    ret=PL_put_float(out,p);
    RETURN_IF_FAIL
    //destroy_table(abdtable,env->n_abd);
    outass=clist_to_pllist(mpa,env);
    RETURN_IF_FAIL
    expl_destroy_table(maptable,env->boolVars);
    destroy_table(table,env->boolVars);
  }
  else
  {
    if (node==Cudd_ReadOne(env->mgr))
    {
      ret=PL_put_float(out,1.0);
      RETURN_IF_FAIL
    }
    else
    {
      ret=PL_put_float(out,0.0);
      RETURN_IF_FAIL
    }
    outass=PL_new_term_ref();
    ret=PL_put_nil(outass);
    RETURN_IF_FAIL
  }

  return(PL_unify(out,arg3)&&PL_unify(outass,arg4));
}

static foreign_t ret_vit_prob(term_t arg1, term_t arg2,
  term_t arg3, term_t arg4)
{
  term_t out,outass;
  environment * env;
  DdNode * node;
  expltablerow * expltable;
  tablerow * table;
  //abdtablerow * abdtable;
  prob_abd_expl delta;
    //abdtable=init_abd_table(env->n_abd);
  int ret;
  double p;
  explan_t * mpa;

  ret=PL_get_pointer(arg1,(void **)&env);
  RETURN_IF_FAIL
  ret=PL_get_pointer(arg2,(void **)&node);
  RETURN_IF_FAIL
  out=PL_new_term_ref();


  if (!Cudd_IsConstant(node))
  {
    expltable=expl_init_table(env->boolVars);
    table=init_table(env->boolVars);
    //abdtable=init_abd_table(env->n_abd);
    delta=vit_Prob(node,env,expltable,table,0);
    p=delta.prob;
    mpa=delta.mpa;
    ret=PL_put_float(out,p);
    RETURN_IF_FAIL
    //destroy_table(abdtable,env->n_abd);
    outass=vit_clist_to_pllist(mpa,env);
    RETURN_IF_FAIL
    expl_destroy_table(expltable,env->boolVars);
    destroy_table(table,env->boolVars);
  }
  else
  {
    if (node==Cudd_ReadOne(env->mgr))
    {
      ret=PL_put_float(out,1.0);
      RETURN_IF_FAIL
    }
    else
    {
      ret=PL_put_float(out,0.0);
      RETURN_IF_FAIL
    }
      outass=PL_new_term_ref();
      ret=PL_put_nil(outass);
      RETURN_IF_FAIL
  }

  return(PL_unify(out,arg3)&&PL_unify(outass,arg4));
}
static foreign_t make_query_var(term_t arg1, term_t arg2, term_t arg3)
{
  environment * env;
  int ret,varIndex,i,j;
  DdNode * cons, * tmp0,* tmp1, * tmp2, * vari, * varlast, * varj, * or, * tmpor;
  term_t out;
  variable var;

  ret=PL_get_pointer(arg1,(void **)&env);
  RETURN_IF_FAIL
  ret=PL_get_integer(arg2,&varIndex);
  /*  printf(" V = varIndex = %d\n",varIndex); */
  RETURN_IF_FAIL

  var=env->vars[varIndex];

  cons=Cudd_ReadOne(env->mgr);
  or=Cudd_ReadLogicZero(env->mgr);

  for (i=var.firstBoolVar; i<var.firstBoolVar+var.nVal-1; i++)
  {    
    vari=Cudd_bddIthVar(env->mgr,i);
    tmpor=Cudd_bddOr(env->mgr,or,vari);
    Cudd_Ref(tmpor);
    Cudd_RecursiveDeref(env->mgr,or);
    or=tmpor;
    for(j=i+1; j<var.firstBoolVar+var.nVal; j++)
    {      
      varj=Cudd_bddIthVar(env->mgr,j);
      tmp0=Cudd_bddAnd(env->mgr,vari,varj);
      Cudd_Ref(tmp0);//added
      tmp1=Cudd_Not(tmp0);
      Cudd_Ref(tmp1);//added
      tmp2=Cudd_bddAnd(env->mgr,cons,tmp1);
      Cudd_Ref(tmp2);
      cons=tmp2;
      Cudd_Ref(cons);//added
    }
  }
  varlast=Cudd_bddIthVar(env->mgr,var.firstBoolVar+var.nVal-1);
  tmpor=Cudd_bddOr(env->mgr,or,varlast);
  Cudd_Ref(tmpor);
  Cudd_RecursiveDeref(env->mgr,or);
  tmp1=Cudd_bddAnd(env->mgr,cons,tmpor);
  Cudd_Ref(tmp1);
  Cudd_RecursiveDeref(env->mgr,cons);
  cons=tmp1;

  out=PL_new_term_ref();
  ret=PL_put_pointer(out,(void *)cons);
  RETURN_IF_FAIL
  return(PL_unify(out,arg3));
}

term_t abd_clist_to_pllist(explan_t *mpa)
{
  term_t out,tail,head,var,val;
  functor_t minus;
  assign a;
  minus=PL_new_functor(PL_new_atom("-"), 2);
  out=PL_new_term_ref();
  head=PL_new_term_ref();
  int ret;
  if (mpa==NULL)
  {
    ret=PL_put_nil(out);
    RETURN_IF_FAIL
  }
  else
  {
    tail=abd_clist_to_pllist(mpa->next);
    a=mpa->a;
    var=PL_new_term_ref();
    val=PL_new_term_ref();
    ret=PL_put_integer(var,a.var);
    RETURN_IF_FAIL
    ret=PL_put_integer(val,a.val);
    RETURN_IF_FAIL
    ret=PL_cons_functor(head, minus,var,val);
    RETURN_IF_FAIL
    ret=PL_cons_list(out,head,tail);
    RETURN_IF_FAIL
  }
  return out;
}
term_t clist_to_pllist(explan_t *mpa, environment * env)
{
  term_t out,tail,head,var,val;
  functor_t minus;
  assign a;
  int value,bvar, ret, mvari, mval;
  variable mvar;

  minus=PL_new_functor(PL_new_atom("-"), 2);
  tail=PL_new_term_ref();
  ret=PL_put_nil(tail);
  RETURN_IF_FAIL
  if (mpa==NULL)
  {
    out=PL_new_term_ref();
    ret=PL_put_nil(out);
    RETURN_IF_FAIL
  }
  else
  {

    for (; mpa; mpa=mpa->next)
    {
      a=mpa->a;
      bvar=a.var;
      value=a.val;
      if (value)
      {
        mvari=env->bVar2mVar[bvar];
        mvar=env->vars[mvari];
        mval=a.var-mvar.firstBoolVar+1;
        var=PL_new_term_ref();
        val=PL_new_term_ref();
        ret=PL_put_integer(var,mvari);
        RETURN_IF_FAIL
        ret=PL_put_integer(val,mval);
        RETURN_IF_FAIL
        head=PL_new_term_ref();
        ret=PL_cons_functor(head, minus,var,val);
        RETURN_IF_FAIL
        out=PL_new_term_ref();
        ret=PL_cons_list(out,head,tail);
        RETURN_IF_FAIL
        tail=out;
      }
    }
    out=tail;
  }
  return out;
}

term_t vit_clist_to_pllist(explan_t *mpa, environment * env)
{
  term_t out,tail,head,var,val;
  functor_t minus;
  assign a;
  int value,bvar, ret, mvari, mval,nVars,i,*assignments;
  variable mvar;

  if (mpa==NULL)
  {
    out=PL_new_term_ref();
    ret=PL_put_nil(out);
    RETURN_IF_FAIL
  }
  else
  {
    nVars=env->nVars;
    assignments=malloc(nVars*sizeof(int));
    for (i=0;i<nVars;i++)
      assignments[i]=-1;

    for (; mpa; mpa=mpa->next)
    {
      a=mpa->a;
      bvar=a.var;
      value=a.val;
      mvari=env->bVar2mVar[bvar];
      mvar=env->vars[mvari];
      if (value)
      {
        mval=a.var-mvar.firstBoolVar;
        assignments[mvari]=mval;
      }
      else
      {
        assignments[mvari]=env->vars[mvari].nVal-1;
      }
    }
    minus=PL_new_functor(PL_new_atom("-"), 2);
    tail=PL_new_term_ref();
    ret=PL_put_nil(tail);
    RETURN_IF_FAIL
    for (i=0;i<nVars;i++)
    {
      if (assignments[i]!=-1)
      {
        var=PL_new_term_ref();
        val=PL_new_term_ref();
        ret=PL_put_integer(var,i);
        RETURN_IF_FAIL
        ret=PL_put_integer(val,assignments[i]);
        RETURN_IF_FAIL
        head=PL_new_term_ref();
        ret=PL_cons_functor(head, minus,var,val);
        RETURN_IF_FAIL
        out=PL_new_term_ref();
        ret=PL_cons_list(out,head,tail);
        RETURN_IF_FAIL
        tail=out;
      }
    }
    out=tail;
  }
  return out;
}

double Prob(DdNode *node, environment * env, tablerow * table)
/* compute the probability of the expression rooted at node.
table is used to store nodeB for which the probability has already been computed
so that it is not recomputed
 */
{
  int index;
  double res;
  double p,pt,pf,BChild0,BChild1;
  double * value_p;
  DdNode *nodekey,*T,*F;
  //comp=(comp && !comp_par) ||(!comp && comp_par);
  if (Cudd_IsConstant(node))
  {
      return 1.0;
  }
  else
  {
    nodekey=Cudd_Regular(node);
    value_p=get_value(table,nodekey);
    if (value_p!=NULL)
        return *value_p;
    else
    {
      index=Cudd_NodeReadIndex(node);  //Returns the index of the node. The node pointer can be either regular or complemented.
      //The index field holds the name of the variable that labels the node. The index of a variable is a permanent attribute that reflects the order of creation.
      p=env->probs[index];
      T = Cudd_T(node);
      F = Cudd_E(node);
      pf=Prob(F,env,table);
      pt=Prob(T,env,table);
      if (Cudd_IsComplement(F))
        pf=1.0-pf;

      BChild0=pf*(1-p);
      BChild1=pt*p;
      res=BChild0+BChild1;
      add_node(table,nodekey,res);
      return res;
    }
  }
}

prob_abd_expl abd_Prob(DdNode *node, environment * env,
  expltablerow * expltable, tablerow * table,
  int comp_par)
/* compute the probability of the expression rooted at node.
table is used to store nodeB for which the probability has already been computed
so that it is not recomputed
 */
{
  int index,comp,pos;
  double p,p0,p1;
  DdNode *nodekey,*T,*F;
  prob_abd_expl deltat,deltaf,delta,*deltaptr;
  assign assignment;
  explan_t * mpa0,* mpa1,* mpa;
  explan_t *mptemp;

  comp = Cudd_IsComplement(node);
  comp=(comp && !comp_par) ||(!comp && comp_par);
  if(Cudd_IsConstant(node)) {
    p1 = 1;
    if (comp)
      p1= 1.0-p1;

    delta.prob=p1;
    delta.mpa=NULL;

    return delta;
  }
  index=Cudd_NodeReadIndex(node);
  pos=Cudd_ReadPerm(env->mgr,index);
  if (pos>=env->n_abd_boolVars)
  {
    p1=Prob(node,env,table);
    if (comp)
      p1= 1.0-p1;

    delta.prob=p1;
    delta.mpa=NULL;

    return delta;
  }
  else
  {
    nodekey=Cudd_Regular(node);
    deltaptr=expl_get_value(expltable,nodekey,comp);
    if (deltaptr!=NULL)
    {
      return *deltaptr;
    }
    else
    {

      T = Cudd_T(node);
      F = Cudd_E(node);
      deltaf=abd_Prob(F,env,expltable,table,comp);
      deltat=abd_Prob(T,env,expltable,table,comp);
      p=env->probs[index];

      if (p==1.0)
      {
        p0=deltaf.prob;
        p1=deltat.prob;
      }
      else
      {
        p0=deltaf.prob;
        p1=deltat.prob*p + deltaf.prob*(1-p);
      }

      mpa0=deltaf.mpa;
      mpa1=deltat.mpa;

      assignment.var=env->bVar2mVar[index];
      if (p1>p0) {
        assignment.val=1;

        if(p != 0 && p != 1) {
          mptemp = merge_explain(mpa0,mpa1);
          mpa = insert(assignment,mptemp);
          // free(mptemp);
          // all the list must be freed
        }
        else {
          mpa=insert(assignment,mpa1);
        }
        delta.prob=p1;
      }
      else
      {
        assignment.val=0;
        mpa=insert(assignment,mpa0);
        delta.prob=p0;
      }
      delta.mpa=mpa;
      expl_add_node(expltable,nodekey,comp,delta);
      return delta;
    }
  }
}

prob_abd_expl map_Prob(DdNode *node, environment * env,
  expltablerow * maptable, tablerow * table,
  int comp_par)
/* compute the probability of the expression rooted at node.
table is used to store nodeB for which the probability has already been computed
so that it is not recomputed
 */
{
  int index,comp,pos;
  double p,p0,p1;
  DdNode *nodekey,*T,*F;
  prob_abd_expl deltat,deltaf,delta,*deltaptr;
  assign assignment;
  explan_t * mpa0,* mpa1,* mpa;


  index=Cudd_NodeReadIndex(node);
  pos=Cudd_ReadPerm(env->mgr,index);
  comp=Cudd_IsComplement(node);
  comp=(comp && !comp_par) ||(!comp && comp_par);

  if (pos>=env->n_abd_boolVars)
  {
    p1=Prob(node,env,table);
    if (comp)
      p1= 1.0-p1;
    delta.prob=p1;
    delta.mpa=NULL;


    return delta;
  }
  else
  {
    nodekey=Cudd_Regular(node);
    deltaptr=expl_get_value(maptable,nodekey,comp);
    if (deltaptr!=NULL)
    {
      return *deltaptr;
    }
    p=env->probs[index];
    T = Cudd_T(node);
    F = Cudd_E(node);
    deltaf=map_Prob(F,env,maptable,table,comp);
    deltat=map_Prob(T,env,maptable,table,comp);

    p0=deltaf.prob;
    mpa0=deltaf.mpa;

    p1=deltat.prob*p;
    mpa1=deltat.mpa;

    if (p1>p0)
    {
      assignment.var=index;
      assignment.val=1;
      mpa=insert(assignment,mpa1);
      delta.prob=p1;
      delta.mpa=mpa;
    }
    else
    {
      assignment.var=index;
      assignment.val=0;
      mpa=insert(assignment,mpa0);
      delta.prob=p0;
      delta.mpa=mpa;
    }
    expl_add_node(maptable,nodekey,comp,delta);
    return delta;
  }

}
prob_abd_expl vit_Prob(DdNode *node, environment * env,
  expltablerow * expltable, tablerow * table,
  int comp_par)
/* compute the probability of the expression rooted at node.
table is used to store nodeB for which the probability has already been computed
so that it is not recomputed
 */
{
  int index,comp;
  double p,p0,p1;
  DdNode *nodekey,*T,*F;
  prob_abd_expl deltat,deltaf,delta,*deltaptr;
  assign assignment;
  explan_t * mpa0,* mpa1,* mpa;

  comp=Cudd_IsComplement(node);
  comp=(comp && !comp_par) ||(!comp && comp_par);
  index=Cudd_NodeReadIndex(node);
  if (Cudd_IsConstant(node))
  {

    if (comp)
      p1= 0.0;
    else
      p1= 1.0;

    delta.prob=p1;
    delta.mpa=NULL;

    return delta;
  }
  else
  {
    nodekey=Cudd_Regular(node);
    deltaptr=expl_get_value(expltable,nodekey,comp);
    if (deltaptr!=NULL)
    {
      return *deltaptr;
    }
    else
    {

      T = Cudd_T(node);
      F = Cudd_E(node);
      deltaf=vit_Prob(F,env,expltable,table,comp);
      deltat=vit_Prob(T,env,expltable,table,comp);
      p=env->probs[index];


      p0=deltaf.prob*(1-p);
      p1=deltat.prob*p;

      mpa0=deltaf.mpa;
      mpa1=deltat.mpa;

      if (p1>p0)
      {
        assignment.var=index;
        assignment.val=1;
        mpa=insert(assignment,mpa1);
        delta.prob=p1;
        delta.mpa=mpa;
      }
      else
      {
        assignment.var=index;
        assignment.val=0;
        mpa=insert(assignment,mpa0);
        delta.prob=p0;
        delta.mpa=mpa;
      }
      expl_add_node(expltable,nodekey,comp,delta);
      return delta;
    }
  }
}

int in_list(explan_t *list, assign element) {
  while (list != NULL) {
    if(list->a.var == element.var) {
      return 1;
    }
    list = list->next;
  }
  return 0;
}

explan_t *merge_explain(explan_t *a, explan_t *b) {
  explan_t *init = NULL;
  explan_t *root = NULL;
  
  if(a == NULL && b == NULL) {
    return NULL;
  }
  if(a == NULL) {
    return duplicate(b);
  }
  if(b == NULL) {
    return duplicate(a);
  }

  // printf("merging a\n");
  while(a != NULL) {
    init = malloc(sizeof(explan_t));
    init->a = a->a;
    init->next = root;
    root = init;
    a = a->next;
  }

  // printf("merging b\n");
  // not super fast, but it is simple to implement
  while(b != NULL) {
    if(in_list(root,b->a) <= 0) {
      init = malloc(sizeof(explan_t));
      init->a = b->a;
      init->next = root;
      root = init;
    } 
    b = b->next;
  }

  return root;
}

explan_t * insert(assign assignment,explan_t * head)
{
  explan_t * newhead;

  newhead=malloc(sizeof(explan_t));
  newhead->a=assignment;
  newhead->next=duplicate(head);
  return newhead;
}

explan_t * duplicate(explan_t * head)
{
  explan_t * newhead;
  if (head)
  {
    newhead=malloc(sizeof(explan_t));
    newhead->a=head->a;
    newhead->next=duplicate(head->next);
  }
  else
    newhead=NULL;
  return newhead;
}

void free_list(explan_t * head)
{
  if (head)
  {
    free_list(head->next);
    free(head);
  }
}
static foreign_t add_var(term_t arg1,term_t arg2,term_t arg3,term_t arg4)
{
  term_t out,head,probTerm;
  variable * v;
  int i,ret,nRules;
  size_t lenProbs;
  double p,p0;
  environment * env;

  head=PL_new_term_ref();
  out=PL_new_term_ref();
  ret=PL_get_pointer(arg1,(void **)&env);
  RETURN_IF_FAIL
  env->nVars=env->nVars+1;
  env->vars=(variable *) realloc(env->vars,env->nVars * sizeof(variable));

  v=&env->vars[env->nVars-1];
  v->abducible=0;
  v->query=0;
  v->decision=0;
  v->optimize = 0;

  ret=PL_get_integer(arg3,&v->nRule);
  RETURN_IF_FAIL
  probTerm=PL_copy_term_ref(arg2);
  ret=PL_skip_list(probTerm,0,&lenProbs);
  if (ret!=PL_LIST) return FALSE;

  // printf("len prob: %d\n",lenProbs);

  v->nVal=lenProbs;
  nRules=env->nRules;
  if (v->nRule>=nRules)
  {
    env->rules=(int *)  realloc(env->rules,((v->nRule+1)* sizeof(int)));
    for (i=nRules;i<v->nRule;i++)
      env->rules[i]=0;
    env->rules[v->nRule]=lenProbs;
    env->nRules=v->nRule+1;
  }
  v->firstBoolVar=env->boolVars;
  env->probs=(double *) realloc(env->probs,(((env->boolVars+v->nVal-1)* sizeof(double))));
  env->bVar2mVar=(int *) realloc(env->bVar2mVar,((env->boolVars+v->nVal-1)* sizeof(int)));

  p0=1;
  for (i=0;i<v->nVal-1;i++)
  {
    ret=PL_get_list(probTerm,head,probTerm);
    RETURN_IF_FAIL
    ret=PL_get_float(head,&p);
    RETURN_IF_FAIL
    env->bVar2mVar[env->boolVars+i]=env->nVars-1;
    env->probs[env->boolVars+i]=p/p0;
    p0=p0*(1-p/p0);
  }
  env->boolVars=env->boolVars+v->nVal-1;
  env->rules[v->nRule]= v->nVal;

  ret=PL_put_integer(out,env->nVars-1);
  RETURN_IF_FAIL

  return(PL_unify(out,arg4));
}

static foreign_t add_query_var(term_t arg1,term_t arg2,term_t arg3,term_t arg4)
{
  term_t out,head,probTerm;
  variable * v;
  int i,ret,nRules;
  size_t lenProbs;
  double p;
  environment * env;

  head=PL_new_term_ref();
  out=PL_new_term_ref();
  ret=PL_get_pointer(arg1,(void **)&env);
  RETURN_IF_FAIL
  env->nVars=env->nVars+1;
  env->n_abd++;
  env->vars=(variable *) realloc(env->vars,env->nVars * sizeof(variable));

  v=&env->vars[env->nVars-1];
  v->query=1;
  v->abducible=0;
  v->decision=0;

  probTerm=PL_copy_term_ref(arg2);

  ret=PL_skip_list(probTerm,0,&lenProbs);
  if (ret!=PL_LIST) return FALSE;
  v->nVal=lenProbs;

  ret=PL_get_integer(arg3,&v->nRule);
  RETURN_IF_FAIL
  nRules=env->nRules;
  if (v->nRule>=nRules)
  {
    env->rules=(int *)  realloc(env->rules,((v->nRule+1)* sizeof(int)));
    for (i=nRules;i<v->nRule;i++)
      env->rules[i]=0;
    env->rules[v->nRule]=lenProbs;
    env->nRules=v->nRule+1;
  }

  env->n_abd_boolVars=env->n_abd_boolVars+v->nVal;
  v->firstBoolVar=env->boolVars;
  env->probs=(double *) realloc(env->probs,(((env->boolVars+v->nVal)* sizeof(double))));
  env->bVar2mVar=(int *) realloc(env->bVar2mVar,((env->boolVars+v->nVal)* sizeof(int)));

  for (i=0;i<v->nVal;i++)
  {
    ret=PL_get_list(probTerm,head,probTerm);
    RETURN_IF_FAIL
    ret=PL_get_float(head,&p);
    RETURN_IF_FAIL
    env->bVar2mVar[env->boolVars+i]=env->nVars-1;
    env->probs[env->boolVars+i]=p;
  }
  env->boolVars=env->boolVars+v->nVal;
  env->rules[v->nRule]= v->nVal;

  ret=PL_put_integer(out,env->nVars-1);
  RETURN_IF_FAIL

  return(PL_unify(out,arg4));
}

static foreign_t add_decision_var(term_t env_ref,term_t current_n_rule,term_t vout) {
  term_t out;
  variable * v;
  int i,ret,nRules;
  environment * env;

  out = PL_new_term_ref();
  ret = PL_get_pointer(env_ref,(void **)&env);
  RETURN_IF_FAIL

  env->nVars = env->nVars+1; // increase the counter of multival var
  env->vars = (variable *) realloc(env->vars,env->nVars * sizeof(variable));

  v = &env->vars[env->nVars-1];
  v->query = 0;
  v->abducible = 0;
  v->decision = 1; // set decision var

  v->nVal = 2; // yes or no

  ret = PL_get_integer(current_n_rule,&v->nRule);
  RETURN_IF_FAIL
  
  nRules=env->nRules;
  if (v->nRule>=nRules) {
    env->rules = (int *)  realloc(env->rules,((v->nRule+1)* sizeof(int)));
    for (i=nRules;i<v->nRule;i++)
      env->rules[i] = 0;
    env->rules[v->nRule] = 2;
    env->nRules = v->nRule + 1;
  }

  v->firstBoolVar = env->boolVars;
  env->probs = (double *) realloc(env->probs,(((env->boolVars+v->nVal-1)* sizeof(double))));
  env->bVar2mVar = (int *) realloc(env->bVar2mVar,((env->boolVars+v->nVal-1)* sizeof(int)));

  env->bVar2mVar[env->boolVars] = env->nVars-1;
  env->probs[env->boolVars] = -1; // set the prob of decision var to -1 
  
  env->boolVars = env->boolVars + 1; // v->nVal-1 = 2 - 1 = 1 ; // increases the number of bool vars
  env->rules[v->nRule] = 2; // v->nVal = 2; // set the number of heads

  ret=PL_put_integer(out,env->nVars-1);
  RETURN_IF_FAIL

  return(PL_unify(out,vout));
}

int compare_utils(const void *a, const void *b) {
  if ((*(const node_impact*)a).impact < (*(const node_impact*)b).impact) {
    return 1;
  }
  else if ((*(const node_impact*)a).impact > (*(const node_impact*)b).impact) {
    return -1;
  }
  else {
    return 0;
  }
}

DdNode* setLowerBound(DdManager *dd, DdNode *current_node, double lowerBound) {
	DdNode *res, *then_branch, *else_branch, *T, *E;
	if (Cudd_IsConstant(current_node)) {
		if(Cudd_V(current_node) < lowerBound) {
      // printf("Pruned\n");
      res = Cudd_addConst(dd,MINUS_INF);
      Cudd_Ref(res);
			return res;
		}
    else {
      res = current_node;
      // Cudd_Ref(res);
      return res;
    }
	}

	then_branch = Cudd_T(current_node);
	else_branch = Cudd_E(current_node);

	T = setLowerBound(dd,then_branch,lowerBound);
	if (T == NULL) {
	   return NULL;
	}
	Cudd_Ref(T);
	E = setLowerBound(dd,else_branch,lowerBound);
	if (E == NULL) {
		// Cudd_RecursiveDeref(dd,T);
		return NULL;
	}
	Cudd_Ref(E);
  if(T == E) {
    res = T;
    // Cudd_Ref(res);
  }
  else {
    res = current_node;
  }

	if (res == NULL) {
		Cudd_RecursiveDeref(dd,T);
		Cudd_RecursiveDeref(dd,E);
		return(NULL);
	}
  // Cudd_Ref(res);

	Cudd_Deref(T);
	Cudd_Deref(E);

	return res;
}


static foreign_t compute_best_strategy(term_t env_ref, term_t b_list, term_t u_list, term_t strategy_list, term_t cost) {
  int ret, i = 0, len_array_of_parents = 0, j = 0;
  // int n_zero_impact = 0; // numbers of utility facts with 0 impact
  int *array_of_parents = NULL; // array containing the indexes of the encountered parents
  double current_cost, utility_sum = 0, value = -1.0;
  DdNode *root = NULL, *add_sum = NULL , *temp = NULL, *max_node = NULL, *bestNode = NULL, *current_root = NULL, *constant = NULL, *root_pre = NULL, *add_one = NULL;
  term_t head_bdd = PL_new_term_ref();   /* the elements */
  term_t head_util = PL_new_term_ref();
  term_t bdd_list = PL_copy_term_ref(b_list); /* copy (we modify list) */
  term_t util_list = PL_copy_term_ref(u_list); /* copy (we modify list) */
  term_t outcost=PL_new_term_ref();
  term_t list, head;
  size_t nutils;
  node_impact *list_impacts;
  environment *env;

  ret = PL_get_pointer(env_ref,(void **)&env);
  RETURN_IF_FAIL

  ret=PL_skip_list(bdd_list,0,&nutils);
  if (ret!=PL_LIST) return FALSE;

  list = PL_new_term_ref();
  head = PL_new_term_ref();
  ret = PL_put_nil(list);
  RETURN_IF_FAIL

  list_impacts = malloc(sizeof(node_impact)*(int)nutils);

  // initialize the memory to NULL
  for(j = 0; j < nutils; j++) {
    list_impacts[j].root = NULL;
    list_impacts[j].impact = -1000;
  }


  while(PL_get_list(bdd_list, head_bdd, bdd_list) && PL_get_list(util_list, head_util, util_list)) {
    if(i >= nutils) {
      printf("Error in nutils\n");
      return -1;
    }
    ret=PL_get_pointer(head_bdd,(void **)&current_root);
    RETURN_IF_FAIL

    if(current_root == NULL) {
      printf("Current root NULL\n");
      return -1;
    }

    ret=PL_get_float(head_util,&current_cost);
    RETURN_IF_FAIL

    root_pre = NULL;
    
    root_pre = Probability_dd_bdd(env,current_root);
    if(root_pre != NULL) {
      Cudd_Ref(root_pre); // <--- 
    }
    else {
      printf("Root pre NULL\n");
      return -1;
    }

    if(Cudd_IsComplement(current_root)) {
      add_one = Cudd_addConst(env->mgr,(CUDD_VALUE_TYPE) 1);
      Cudd_Ref(add_one);
      root = Cudd_addApply(env->mgr,Cudd_addMinus,add_one,root_pre);
      Cudd_Ref(root);
      Cudd_RecursiveDeref(env->mgr,add_one);
      Cudd_RecursiveDeref(env->mgr,root_pre);
    }
    else {
      root = root_pre;
      Cudd_Ref(root);
      Cudd_RecursiveDeref(env->mgr,root_pre);
    }
    // Cudd_Ref(root);
    // Cudd_RecursiveDeref(env->mgr,root_pre);

    Cudd_RecursiveDeref(env->mgr,current_root);

    // Cudd_Ref(root);
    // printf("Root - DdNode nodes: %d \n", Cudd_DagSize(root_pre)); /*Reports the number of nodes in the BDD*/
    
    // Cudd_PrintDebug(env->mgr, root, 2, 4);
    constant = Cudd_addConst(env->mgr,(CUDD_VALUE_TYPE)current_cost);
		Cudd_Ref(constant);
		list_impacts[i].root = Cudd_addApply(env->mgr,Cudd_addTimes,root,constant);
    Cudd_Ref(list_impacts[i].root);
 
    Cudd_RecursiveDeref(env->mgr,constant);
    Cudd_RecursiveDeref(env->mgr,root);

    double max_v, min_v;
    max_v = Cudd_V(Cudd_addFindMax(env->mgr,list_impacts[i].root));
    list_impacts[i].impact = max_v;
    min_v = Cudd_V(Cudd_addFindMin(env->mgr,list_impacts[i].root));
    list_impacts[i].impact += -min_v;

    utility_sum += list_impacts[i].impact; 

     //Cudd_PrintDebug(env->mgr, list_impacts[i].root, 2, 4);

    // not consider the utility facts with impact 0
    // if(list_impacts[i].impact == 0 && max_v == 0) {
    //   n_zero_impact++;
    //   // Cudd_RecursiveDeref(env->mgr,list_impacts[i].root);
    //   printf("Pruned\n");
    // }
    // else {
    //   Cudd_Ref(list_impacts[i].root);
    // }
    i++;
  }

  if(i != nutils) {
    printf("i != nutils\n");
    return -1;
  }
  // update nutils
  // nutils = nutils - n_zero_impact;
  
  // nutils = i;
  
  
  qsort(list_impacts,nutils,sizeof(node_impact),compare_utils);  

  if(DEBUG) {
    printf("nutils: %d \n",(int)nutils);
    for(i = 0; i < (int)nutils; i++) {
      printf("Impact %d -> %lf\n",i,list_impacts[i].impact);
    }
  }
  

  add_sum = Cudd_addConst(env->mgr,(CUDD_VALUE_TYPE)0);
	Cudd_Ref(add_sum);
  // printf("utility_sum: %lf\n",utility_sum);
  if(DEBUG) {
    printf("\n\nCYCLE\n\n");
    debug_cudd_env(env,0);
  }
  
  for(i = 0; i < (int)nutils; i++) {
    if(DEBUG) {
      debug_cudd_env(env,0);    
    }
    temp = Cudd_addApply(env->mgr,Cudd_addPlus,add_sum,list_impacts[i].root);
    Cudd_Ref(temp);
		Cudd_RecursiveDeref(env->mgr,add_sum);
		Cudd_RecursiveDeref(env->mgr,list_impacts[i].root);
		add_sum = temp;
    if(DEBUG) {
      printf("ITERATIONS %d\n",i);
      // Cudd_PrintDebug(env->mgr, add_sum, 2, 4);
      debug_cudd_env(env,0);
    }
    
    if(i < (int)nutils-1) { 
      utility_sum -= list_impacts[i].impact;
			max_node = Cudd_addFindMax(env->mgr,add_sum);
			temp = setLowerBound(env->mgr,add_sum,Cudd_V(max_node)-utility_sum);

			Cudd_Ref(temp);
			Cudd_RecursiveDeref(env->mgr,add_sum);
			add_sum = temp;
		}
  }

  // printf("\n--- FINAL ADD ---\n");
  // Cudd_PrintDebug(env->mgr, add_sum, 2, 4);

  // write_dot(env,temp,"addsum.dot");
  // if(list_impacts) {
  //   free(list_impacts);
  // }

  // find the best strategy
  array_of_parents = (int *)malloc(sizeof(int));

  bestNode = Cudd_addFindMax(env->mgr,add_sum);
  value = Cudd_V(bestNode);
  printf("Value: %lf\n",value);

  // check if found
  if(bestNode == NULL) {
    // no solution found -> return empty list and -1 as cost
    // printf("no solution\n");
    ret = PL_put_integer(outcost,(long)-1);
    RETURN_IF_FAIL
    return PL_unify(outcost,cost);
  } 
  else {
    ret = find_path(add_sum,value,&array_of_parents,&len_array_of_parents);
    if(ret != 1) {
      return ret;
    }
    for (i = 0; i < len_array_of_parents; i++) {
      ret = PL_put_integer(head,array_of_parents[i]); 
      RETURN_IF_FAIL
      ret = PL_cons_list(list,head,list);
      RETURN_IF_FAIL
    }
    ret = PL_put_float(outcost,value);
    RETURN_IF_FAIL
  }

  for(i = 0; i < len_array_of_parents; i++) {
    printf("array_of_parents[%d]: %d\n",i,array_of_parents[i]);
  }

  if(array_of_parents) {
    free(array_of_parents);
  }
  Cudd_RecursiveDeref(env->mgr,add_sum);
 
  return(PL_unify(list,strategy_list)&&PL_unify(cost,outcost));
}


static foreign_t probability_dd(term_t env_ref, term_t bdd_ref, term_t add_out) {
  int ret;
  term_t out;
  DdNode *bdd = NULL, *root = NULL, *add_one = NULL, *root1 = NULL;
  environment *env;

  ret = PL_get_pointer(env_ref,(void **)&env);
  RETURN_IF_FAIL

  ret = PL_get_pointer(bdd_ref,(void **)&bdd);
  RETURN_IF_FAIL

  if(Cudd_IsConstant(bdd)) {
    printf("const val: %lf\n",Cudd_V(bdd));
    root = Cudd_addConst(env->mgr,1);
  }
  else {
    root = Probability_dd_bdd(env,bdd);
    // Cudd_Ref(root);
    if(root == NULL) {
      printf("computed add NULL\n");
      return -1;
    }
  }
  Cudd_Ref(root);

  out = PL_new_term_ref();
  
  if(Cudd_IsComplement(bdd)) {
    add_one = Cudd_addConst(env->mgr,(CUDD_VALUE_TYPE) 1);
    Cudd_Ref(add_one);
    root1 = Cudd_addApply(env->mgr,Cudd_addMinus,add_one,root);
    Cudd_Ref(root1);
    Cudd_RecursiveDeref(env->mgr,add_one);
    Cudd_RecursiveDeref(env->mgr,root);
    // Cudd_RecursiveDeref(env->mgr,root);
    // Cudd_PrintDebug(env->mgr, root1, 2, 4);
    ret = PL_put_pointer(out,(void *)root1);
    RETURN_IF_FAIL
  }
  else {
    // Cudd_PrintDebug(env->mgr, root, 2, 4);
    ret = PL_put_pointer(out,(void *)root);
    RETURN_IF_FAIL
    // Cudd_RecursiveDeref(env->mgr,root);
  }
  Cudd_RecursiveDeref(env->mgr,bdd); // <---


  // // count the number of terminal nodes with the following line:
  // printf("Path: %ld\n",(long)Cudd_CountPath(root1));

  // Cudd_RecursiveDeref(env->mgr,node);
  return(PL_unify(out,add_out));
}

DdNode* Probability_dd_bdd(environment *env, DdNode *current_node) {
  int index;
  int indexMultival;
  double p;
  DdNode *addh, *addl;
  DdNode *nodep, *nodep1;
  DdNode *nodepa, *nodepb;
  DdNode *result, *tmp;
  DdNode *add_one, *addl_new;
  DdNode *E,*T;

  if(current_node == NULL) {
    printf("NODE NULL\n"); 
    return NULL;
  }

  // if is terminal node
  // all terminal nodes of a BDD are 1 nodes
  if(Cudd_IsConstant(current_node)) { 
    // Cudd_Ref(current_node);

    if(Cudd_V(current_node) != 1.0) {
      printf("TERMINAL VALUE != 1.0 -> %lf\n",Cudd_V(current_node));
      return NULL;
    }
    result = Cudd_addConst(env->mgr,(CUDD_VALUE_TYPE) 1);
    if(result == NULL) {
      printf("ADD CONST 1 NULL\n");
      return NULL;
    }
    Cudd_Ref(result);
    return result;
  }

  T = Cudd_T(Cudd_Regular(current_node));
  if(T == NULL) {
    printf("Error in CUDD_T\n");
    return NULL;
  }
  Cudd_Ref(T); // <----- 
  // Cudd_RecursiveDeref(env->mgr,current_node);
  // Cudd_RecursiveDeref(env->mgr,T);

  E = Cudd_E(Cudd_Regular(current_node));
  if(E == NULL) {
    printf("Error in CUDD_E\n");
    return NULL;
  }
  Cudd_Ref(E); // <----- 


  // Cudd_RecursiveDeref(env->mgr,current_node);
  addh = Probability_dd_bdd(env,T);
  if(addh == NULL) {
    printf("ADDH ERROR\n"); 
    return NULL;
  }
  Cudd_Ref(addh);

  addl = Probability_dd_bdd(env,E);  
  if(addl == NULL) {
    printf("ADDL ERROR\n"); 
    return NULL;
  }
  Cudd_Ref(addl);

  if(Cudd_IsComplement(E)) {
    add_one = Cudd_addConst(env->mgr,(CUDD_VALUE_TYPE) 1);
    Cudd_Ref(add_one);
    addl_new = Cudd_addApply(env->mgr,Cudd_addMinus,add_one,addl);
    // Cudd_Ref(addl_new);
    Cudd_RecursiveDeref(env->mgr,add_one);
    Cudd_RecursiveDeref(env->mgr,addl);
  }
  else {
    addl_new = addl;
    // Cudd_Ref(addl_new);
  }
  Cudd_Ref(addl_new);
    Cudd_RecursiveDeref(env->mgr,T);
    Cudd_RecursiveDeref(env->mgr,E);

  // Cudd_RecursiveDeref(env->mgr,addl);
  // Cudd_RecursiveDeref(env->mgr,E);
  
  // get the index of the node = index of bool var
  index = (int)Cudd_NodeReadIndex(current_node);
  if(index >= env->boolVars) {
    printf("INDEX BOOL ERROR\n"); 
    return NULL;
  }
  
  // get the index of the multival var
  indexMultival = env->bVar2mVar[index];
  if(indexMultival >= env->nVars) {
    printf("INDEX MULTIVAR ERROR\n"); 
    return NULL;
  }

  // check if the multival var is decision or prob
  if(env->vars[indexMultival].decision == 1) { // if decision var
    // find the current var by getting its rule number
    // printf("DECISION\n");
    if(DEBUG) {
      if(env->vars[indexMultival].nVal != 2) {
        printf("env->vars[indexMultival].nVal = %d (should be 2)\n",env->vars[indexMultival].nVal);
      } 
    }
    
    tmp = Cudd_addIthVar(env->mgr,env->vars[indexMultival].nRule);
    if(tmp == NULL) {
      printf("ERROR ADDITHVAR\n");
    }
    Cudd_Ref(tmp);
    
    // compute the ite on the decision var
    result = Cudd_addIte(env->mgr,tmp,addh,addl_new);
    if(result == NULL) {
      printf("ERROR ADDITE 1-P\n");
      return NULL;
    }
    Cudd_Ref(result);
    Cudd_RecursiveDeref(env->mgr,tmp); // <---- 
    Cudd_RecursiveDeref(env->mgr,addh);
    Cudd_RecursiveDeref(env->mgr,addl_new);
    return result;
  }
  else if(env->vars[indexMultival].decision == 0){ // probability var
    // find the probability of the var using as index the
    // index of the current node in the ADD

    p = env->probs[index];
    if(p < 0 || p > 1) {
      // p = -1 means decision var. -1 is set in add_decision_var
      printf("ERROR IN PROBABILITY\n");
      return NULL;
    }
    // p = env->probs[env->vars[index].nRule];

    // printf("Prob var with P = %f at index %d\n",p,index);
    nodep = Cudd_addConst(env->mgr,(CUDD_VALUE_TYPE) p);
    if(nodep == NULL) {
      printf("ERROR ADDCONST P\n");
      return NULL;
    }
    Cudd_Ref(nodep);    
    nodepa = Cudd_addApply(env->mgr,Cudd_addTimes,nodep,addh);
    if(nodepa == NULL) {
      printf("ERROR ADDTIMES HIGH\n");
      return NULL;
    }
    Cudd_Ref(nodepa);
    Cudd_RecursiveDeref(env->mgr,addh);
    Cudd_RecursiveDeref(env->mgr,nodep);

    nodep1 = Cudd_addConst(env->mgr,(CUDD_VALUE_TYPE) (1-p));
    if(nodep1 == NULL) {
      printf("ERROR ADDCONST 1-P\n");
      return NULL;
    }
    Cudd_Ref(nodep1);
    
    // Cudd_RecursiveDeref(env->mgr,nodep);
   
    nodepb = Cudd_addApply(env->mgr,Cudd_addTimes,nodep1,addl_new);
    if(nodepb == NULL) {
      printf("ERROR ADDTIMES LOW\n");
      return NULL;
    }
    Cudd_Ref(nodepb);
    Cudd_RecursiveDeref(env->mgr,nodep1);
    Cudd_RecursiveDeref(env->mgr,addl_new);

    result = Cudd_addApply(env->mgr,Cudd_addPlus,nodepa,nodepb);
    if(result == NULL) {
      printf("ERROR ADDAPPLY PLUS\n");
      return NULL;
    }
    Cudd_Ref(result);
    Cudd_RecursiveDeref(env->mgr,nodepa);
    Cudd_RecursiveDeref(env->mgr,nodepb);
    return result;
  }
  else {
    printf("ERROR IN VAR\n");
    return NULL;
  }
}

static foreign_t add_prod(term_t env_ref, term_t add_in, term_t value, term_t add_out) {
  int ret;
  double current_value;
  DdNode *add_const, *current_add, *add_ret;
  environment *env;
  term_t out;

  ret = PL_get_pointer(env_ref,(void **)&env);
  RETURN_IF_FAIL

  ret = PL_get_float(value,&current_value);
  RETURN_IF_FAIL

  ret = PL_get_pointer(add_in,(void **)&current_add);
  RETURN_IF_FAIL

  // printf("Current value: %lf\n",current_value);

  add_const = Cudd_addConst(env->mgr,(CUDD_VALUE_TYPE) current_value);
  RETURN_IF_FAIL
  Cudd_Ref(add_const);
  
  add_ret = Cudd_addApply(env->mgr,Cudd_addTimes,add_const,current_add);
  RETURN_IF_FAIL
  Cudd_Ref(add_ret);
  Cudd_RecursiveDeref(env->mgr,add_const);
  Cudd_RecursiveDeref(env->mgr,current_add);

  out = PL_new_term_ref();
  ret = PL_put_pointer(out,(void *)add_ret);
  RETURN_IF_FAIL

  return(PL_unify(out,add_out)); 
}

static foreign_t add_sum(term_t env_ref, term_t add_A, term_t add_B, term_t add_out) {
  int ret;
  term_t out;
  environment *env;
  DdNode *addA, *addB, *add_ret;

  ret = PL_get_pointer(env_ref,(void **)&env);
  RETURN_IF_FAIL
  ret = PL_get_pointer(add_A,(void **)&addA);
  RETURN_IF_FAIL
  ret = PL_get_pointer(add_B,(void **)&addB);
  RETURN_IF_FAIL

  add_ret = Cudd_addApply(env->mgr,Cudd_addPlus,addA,addB);
  RETURN_IF_FAIL
  Cudd_Ref(add_ret);
  Cudd_RecursiveDeref(env->mgr,addA);
  Cudd_RecursiveDeref(env->mgr,addB);

  out = PL_new_term_ref();
  ret = PL_put_pointer(out,(void *)add_ret);
  RETURN_IF_FAIL

  return(PL_unify(out,add_out));  
}

// static foreign_t add_const(term_t env_ref, term_t val, term_t add_out) {
//   term_t out;
//   DdNode * node;
//   environment *env;
//   int ret,value;

//   ret = PL_get_pointer(env_ref,(void **)&env);
//   RETURN_IF_FAIL
//   ret=PL_get_integer(val,&value);
//   RETURN_IF_FAIL

//   node = Cudd_addConst(env->mgr,value);
//   Cudd_Ref(node);
//   out = PL_new_term_ref();
//   ret=PL_put_pointer(out,(void *) node);
//   RETURN_IF_FAIL
//   return(PL_unify(out,add_out));
// }

static foreign_t ret_strategy(term_t env_ref, term_t add, term_t strategy_list, term_t cost) {
  int ret, i;
  int *array_of_parents; // array containing the indexes of the parents 
  int len_array_of_parents = 0;
  double value = -1;
  double opt_cost;
  term_t list, head;
  DdNode *root, *bestNode = NULL;
  environment *env;

  ret = PL_get_pointer(env_ref,(void **)&env);
  RETURN_IF_FAIL
  ret = PL_get_pointer(add,(void **)&root);
  RETURN_IF_FAIL
  
  list = PL_new_term_ref();
  ret = PL_put_nil(list);
  RETURN_IF_FAIL

  opt_cost = PL_new_term_ref();
  head = PL_new_term_ref();

  if(DEBUG) {  
    printf("Cudd_CheckZeroRef: %d\n",Cudd_CheckZeroRef(env->mgr));
    printf("Max memory: %lu\n",Cudd_ReadMaxMemory(env->mgr));
    printf("DdManager nodes: %ld | ", Cudd_ReadNodeCount(env->mgr)); /*Reports the number of live nodes in BDDs and ADDs*/
    printf("DdManager vars: %d | ", Cudd_ReadSize(env->mgr) ); /*Returns the number of BDD variables in existance*/
    printf("DdNode nodes: %d | ", Cudd_DagSize(root)); /*Reports the number of nodes in the BDD*/
    printf("DdNode vars: %d | ", Cudd_SupportSize(env->mgr, root) ); /*Returns the number of variables in the BDD*/
    printf("DdManager reorderings: %d | ", Cudd_ReadReorderings(env->mgr) ); /*Returns the number of times reordering has occurred*/
    printf("DdManager memory: %ld |\n\n", Cudd_ReadMemoryInUse(env->mgr) ); /*Returns the memory in use by the manager measured in bytes*/
    printf("Cudd_CountLeaves: %d |\n\n", Cudd_CountLeaves(root)); /*Returns the memory in use by the manager measured in bytes*/
    debug_cudd_env(env,0);
    Cudd_PrintDebug(env->mgr, root, 2, 4);
  }

  array_of_parents = malloc(sizeof(int));
  // traverse tree to find terminal nodes
  // traverse_tree(root,&bestNode,&index,&value);
  
  bestNode = Cudd_addFindMax(env->mgr,root);

  // check if found
  if(bestNode == NULL) {
    // no solution found -> return empty list and -1 as cost
    ret = PL_put_integer(opt_cost,(long)-1);
    RETURN_IF_FAIL
    
    return PL_unify(opt_cost,cost);
  } 
  else {
    // find path: root -> terminal
    value = Cudd_V(bestNode);
    ret = find_path(root,value,&array_of_parents,&len_array_of_parents);
    if(ret != 1) {
      return ret;
    }

    for (i = 0; i < len_array_of_parents; i++) {
      ret = PL_put_integer(head,array_of_parents[i]); 
      RETURN_IF_FAIL
      ret = PL_cons_list(list,head,list);
      RETURN_IF_FAIL
    }
    ret = PL_put_float(opt_cost,value);
    RETURN_IF_FAIL
  }

  if(array_of_parents) {
    free(array_of_parents);
  }

  Cudd_RecursiveDeref(env->mgr,root);

  return(PL_unify(list,strategy_list) && (PL_unify(opt_cost,cost)));
}

int find_path(DdNode *node, double value, int **array, int *len) {
  if(node == NULL) {
    return 0;
  }
  if(Cudd_IsConstant(node)) {
    if(Cudd_V(node) == value) {
      return 1;
    }
    else {
      return 0;
    }
  }
  // if found int the branch then (1) -> chosen, add one element
  if(find_path(Cudd_T(node),value, array, len)) {
      *array = realloc(*array, ((*len)+1)*sizeof(int));
      (*array)[*len] = Cudd_NodeReadIndex(node); // mod and find nvar here?
      *len = (*len) + 1;
    return 1;
  }
  else if(find_path(Cudd_E(node),value, array, len)) {
    return 1;
  }
  return 0;
}

// UNUSED
// traverse tree to find terminal node with highest utility
void traverse_tree(DdNode *node, DdNode **bestNode, int *index, double *value) {
  if(Cudd_IsConstant(node) != 1) {
    // non terminal node
    traverse_tree(Cudd_T(node),bestNode,index,value);
    traverse_tree(Cudd_E(node),bestNode,index,value);
  }
  else { // terminal node
    if(Cudd_V(node) > *value) {
      *value = Cudd_V(node);
      *index = Cudd_NodeReadIndex(node);
      *bestNode = node;
    }
  }
}

// // traverse tree to find terminal node with highest utility
// // with bound on the choices:
// // precise = 1: exactly n choices
// // precise = 0: max n choices
// void traverse_tree_depth_bound(DdNode *node, DdNode **bestNode, int *index, double *value, int current_lv, int max_lv, int precise) {
//   if(Cudd_IsConstant(node) != 1) {
//     // non terminal node
//     if(current_lv < max_lv) {
//       current_lv++;
//       traverse_tree_depth_bound(Cudd_T(node),bestNode,index,value,current_lv,max_lv,precise);
//       traverse_tree_depth_bound(Cudd_E(node),bestNode,index,value,current_lv-1,max_lv,precise);
//     }
//     else {
//       traverse_tree_depth_bound(Cudd_E(node),bestNode,index,value,current_lv,max_lv,precise);
//     }
//   }
//   else { // terminal node
//     // printf("Terminal\n");  
//     if((precise == 1 && current_lv == max_lv) || precise == 0) {
//       if(Cudd_V(node) > *value) {
//         *value = Cudd_V(node);
//         *index = Cudd_NodeReadIndex(node);
//         *bestNode = node;
//       }
//     }  
//   }
// }

static foreign_t add_abd_var(term_t arg1,term_t arg2,term_t arg3,term_t arg4)
{
  term_t out,head,probTerm;
  variable * v;
  int i,ret,nRules;
  double p,p0;
  environment * env;
  size_t lenProbs;

  head=PL_new_term_ref();
  out=PL_new_term_ref();
  ret=PL_get_pointer(arg1,(void **)&env);
  RETURN_IF_FAIL
  env->nVars=env->nVars+1;
  env->vars=(variable *) realloc(env->vars,env->nVars * sizeof(variable));

  env->n_abd=env->n_abd+1;

  v=&env->vars[env->nVars-1];

  v->abducible=1;
  v->query=0;
  v->decision = 0;
  probTerm=PL_copy_term_ref(arg2);
  ret=PL_skip_list(probTerm,0,&lenProbs);
  if (ret!=PL_LIST) return FALSE;
  v->nVal=lenProbs;

  ret=PL_get_integer(arg3,&v->nRule);
  RETURN_IF_FAIL
  nRules=env->nRules;
  if (v->nRule>=nRules)
  {
    env->rules=(int *)  realloc(env->rules,((v->nRule+1)* sizeof(int)));
    for (i=nRules;i<v->nRule;i++)
      env->rules[i]=0;
    env->rules[v->nRule]=lenProbs;
    env->nRules=v->nRule+1;
  }
  env->n_abd_boolVars=env->n_abd_boolVars+v->nVal-1;

  v->firstBoolVar=env->boolVars;
  env->probs=(double *) realloc(env->probs,(((env->boolVars+v->nVal-1)* sizeof(double))));
  env->bVar2mVar=(int *) realloc(env->bVar2mVar,((env->boolVars+v->nVal-1)* sizeof(int)));

  p0=1;
  for (i=0;i<v->nVal-1;i++)
  {
    ret=PL_get_list(probTerm,head,probTerm);
    RETURN_IF_FAIL
    ret=PL_get_float(head,&p);
    RETURN_IF_FAIL
    env->bVar2mVar[env->boolVars+i]=env->nVars-1;
    env->probs[env->boolVars+i]=p/p0;
    p0=p0*(1-p/p0);
  }
  env->boolVars=env->boolVars+v->nVal-1;
  env->rules[v->nRule]= v->nVal;
  ret=PL_put_integer(out,env->nVars-1);
  RETURN_IF_FAIL

  return(PL_unify(out,arg4));
}

static foreign_t add_opt_var(term_t arg1,term_t arg2,term_t arg3,term_t arg4)
{
  term_t out,head,probTerm;
  variable * v;
  int i,ret,nRules;
  double p,p0;
  environment * env;
  size_t lenProbs;

  head=PL_new_term_ref();
  out=PL_new_term_ref();
  ret=PL_get_pointer(arg1,(void **)&env);
  RETURN_IF_FAIL
  env->nVars=env->nVars+1;
  env->vars=(variable *) realloc(env->vars,env->nVars * sizeof(variable));

  env->n_abd=env->n_abd+1; // keep this so i can reuse reorder
  env->n_opt=env->n_opt+1;

  v=&env->vars[env->nVars-1];

  v->optimize=1;
  v->abducible=1;
  v->query=0;
  v->decision = 0;
  probTerm=PL_copy_term_ref(arg2);
  ret=PL_skip_list(probTerm,0,&lenProbs);
  if (ret!=PL_LIST) return FALSE;
  v->nVal=lenProbs;

  ret=PL_get_integer(arg3,&v->nRule);
  RETURN_IF_FAIL
  nRules=env->nRules;
  if (v->nRule>=nRules)
  {
    env->rules=(int *)  realloc(env->rules,((v->nRule+1)* sizeof(int)));
    for (i=nRules;i<v->nRule;i++)
      env->rules[i]=0;
    env->rules[v->nRule]=lenProbs;
    env->nRules=v->nRule+1;
  }
  env->n_abd_boolVars=env->n_abd_boolVars+v->nVal-1;
  env->n_opt_boolVars=env->n_opt_boolVars+v->nVal-1;

  v->firstBoolVar=env->boolVars;
  env->probs=(double *) realloc(env->probs,(((env->boolVars+v->nVal-1)* sizeof(double))));
  env->bVar2mVar=(int *) realloc(env->bVar2mVar,((env->boolVars+v->nVal-1)* sizeof(int)));

  p0=1;
  for (i=0;i<v->nVal-1;i++)
  {
    ret=PL_get_list(probTerm,head,probTerm);
    RETURN_IF_FAIL
    ret=PL_get_float(head,&p);
    RETURN_IF_FAIL
    env->bVar2mVar[env->boolVars+i]=env->nVars-1;
    env->probs[env->boolVars+i]=p/p0;
    p0=p0*(1-p/p0);
  }
  env->boolVars=env->boolVars+v->nVal-1;
  env->rules[v->nRule]= v->nVal;
  ret=PL_put_integer(out,env->nVars-1);
  RETURN_IF_FAIL

  return(PL_unify(out,arg4));
}

static foreign_t equality(term_t arg1,term_t arg2,term_t arg3, term_t arg4)
{
  term_t out;
  int varIndex;
  int value;
  int i,ret;
  variable v;
  DdNode * node, * tmp,*var;
  environment * env;

  ret=PL_get_pointer(arg1,(void **)&env);
  RETURN_IF_FAIL

  ret=PL_get_integer(arg2,&varIndex);
  RETURN_IF_FAIL
  ret=PL_get_integer(arg3,&value);
  RETURN_IF_FAIL
  v=env->vars[varIndex];
  i=v.firstBoolVar;
  tmp=Cudd_ReadOne(env->mgr);
  Cudd_Ref(tmp);
  node=NULL;
  if (v.query)
  {
    var=Cudd_bddIthVar(env->mgr,v.firstBoolVar+value);
    node=Cudd_bddAnd(env->mgr,tmp,var);
    Cudd_Ref(node);
  }
  else
  {
    for (i=v.firstBoolVar;i<v.firstBoolVar+value;i++)
    {
      var=Cudd_bddIthVar(env->mgr,i);
      node=Cudd_bddAnd(env->mgr,tmp,Cudd_Not(var));
      Cudd_Ref(node);
      Cudd_RecursiveDeref(env->mgr,tmp);
      tmp=node;
    }
    if (!(value==v.nVal-1))
    {
      var=Cudd_bddIthVar(env->mgr,v.firstBoolVar+value);
      node=Cudd_bddAnd(env->mgr,tmp,var);
      Cudd_Ref(node);
      Cudd_RecursiveDeref(env->mgr,tmp);
    }
  }
  out=PL_new_term_ref();
  ret=PL_put_pointer(out,(void *)node);
  RETURN_IF_FAIL
  return(PL_unify(out,arg4));
}

static foreign_t one(term_t arg1, term_t arg2)
{
  term_t out;
  DdNode * node;
  environment *env;
  int res,ret;

  ret=PL_get_pointer(arg1,(void **)&env);
  RETURN_IF_FAIL

  node =  Cudd_ReadOne(env->mgr);
  Cudd_Ref(node);
  out=PL_new_term_ref();
  ret=PL_put_pointer(out,(void *) node);
  RETURN_IF_FAIL
  res=PL_unify(out,arg2);
  return res;

//  return(PL_unify(out,arg2));
}

static foreign_t zero(term_t arg1, term_t arg2)
{
  term_t out;
  DdNode * node;
  environment *env;
  int ret;

  ret=PL_get_pointer(arg1,(void **)&env);
  RETURN_IF_FAIL

  node = Cudd_ReadLogicZero(env->mgr);
  Cudd_Ref(node);
  out=PL_new_term_ref();
  ret=PL_put_pointer(out,(void *) node);
  RETURN_IF_FAIL
  return(PL_unify(out,arg2));
}

// arg1 (env ref) unused
static foreign_t bdd_not(term_t arg1,term_t arg2, term_t arg3)
{
  term_t out;
  DdNode * node;
  int ret;

  ret=PL_get_pointer(arg2,(void **)&node);
  RETURN_IF_FAIL
  node=Cudd_Not(node);
  out=PL_new_term_ref();
  ret=PL_put_pointer(out,(void *) node);
  RETURN_IF_FAIL
  return(PL_unify(out,arg3));
}

static foreign_t and(term_t arg1,term_t arg2,term_t arg3, term_t arg4)
{
  term_t out;
  DdNode * node1, *node2,*nodeout;
  environment *env;
  int res,ret;
  ret=PL_get_pointer(arg1,(void **)&env);
  RETURN_IF_FAIL

  ret=PL_get_pointer(arg2,(void **)&node1);
  RETURN_IF_FAIL
  ret=PL_get_pointer(arg3,(void **)&node2);
  RETURN_IF_FAIL
  nodeout=Cudd_bddAnd(env->mgr,node1,node2);
  Cudd_Ref(nodeout);
  out=PL_new_term_ref();
  ret=PL_put_pointer(out,(void *) nodeout);
  RETURN_IF_FAIL
  res=PL_unify(out,arg4);
  return res;
}

static foreign_t or(term_t arg1,term_t arg2,term_t arg3, term_t arg4)
{
  term_t out;
  DdNode * node1, *node2,*nodeout;
  environment *env;
  int ret;

  ret=PL_get_pointer(arg1,(void **)&env);
  RETURN_IF_FAIL

  ret=PL_get_pointer(arg2,(void **)&node1);
  RETURN_IF_FAIL
  ret=PL_get_pointer(arg3,(void **)&node2);
  RETURN_IF_FAIL

  nodeout=Cudd_bddOr(env->mgr,node1,node2);
  Cudd_Ref(nodeout);
  out=PL_new_term_ref();
  ret=PL_put_pointer(out,(void *) nodeout);
  RETURN_IF_FAIL
  return(PL_unify(out,arg4));
}

/*
static int garbage_collect(void)
{
  YAP_Term arg1,arg2,out;
  YAP_Int nodes,clearCache;

  arg1=YAP_ARG1;
  arg2=YAP_ARG2;
  clearCache=YAP_IntOfTerm(arg1);
  nodes=(YAP_Int)cuddGarbageCollect(mgr_ex[ex],clearCache);
  out=YAP_MkIntTerm(nodes);
  return(YAP_Unify(out,arg2));
}

static int bdd_to_add(void)
{
  YAP_Term arg1,arg2,out;
  DdNode * node1,*node2;

  arg1=YAP_ARG1;
  arg2=YAP_ARG2;
  node1=(DdNode *)YAP_IntOfTerm(arg1);
  node2= Cudd_BddToAdd(mgr_ex[ex],node1);
  out=YAP_MkIntTerm((YAP_Int) node2);
  return(YAP_Unify(out,arg2));
}
*/
static foreign_t create_dot(term_t arg1, term_t arg2, term_t arg3)
{
  DdNode * node;
  environment *env;
  char *filename;
  FILE * file;
  int ret;
  ret=PL_get_pointer(arg1,(void **)&env);
  RETURN_IF_FAIL
  ret=PL_get_pointer(arg2,(void **)&node);
  RETURN_IF_FAIL
  ret=PL_get_file_name(arg3,&filename,0);
  RETURN_IF_FAIL
  file = open_file(filename, "w");
  write_dot(env,node,file);
  fclose(file);
  return TRUE;
}

static foreign_t create_dot_string(term_t arg1, term_t arg2, term_t arg3)
{
  term_t out;
  DdNode * node;
  environment *env;
  FILE * file;
  char *buffer=NULL;
  int ret;

  ret=PL_get_pointer(arg1,(void **)&env);
  RETURN_IF_FAIL
  ret=PL_get_pointer(arg2,(void **)&node);
  RETURN_IF_FAIL
  out=PL_new_term_ref();

#ifndef _WIN32
  file=tmpfile();
#else
  char filename[MAX_PATH];
  GetTempFileName(".","temp",0,filename);
  file = fopen(filename,"w+bTD");
#endif
  if (file==NULL) {perror("Error in temporary file opening");}
  write_dot(env,node,file);

  if (fseek(file, 0L, SEEK_END) == 0) {
    /* Get the size of the file. */
    long bufsize = ftell(file);
    if (bufsize == -1) { perror("Error in getting the size of the temporary file");}

      /* Allocate our buffer to that size. */
        buffer = malloc(sizeof(char) * (bufsize + 1));

        /* Go back to the start of the file. */
        if (fseek(file, 0L, SEEK_SET) != 0) { perror("Error going back to the start of the file");}

        /* Read the entire file into memory. */
        size_t newLen = fread(buffer, sizeof(char), bufsize, file);
        if ( ferror( file ) != 0 ) {
            perror("Error reading file");
        } else {
            buffer[newLen++] = '\0'; /* Just to be safe. */
        }
  }
  fclose(file);
  ret=PL_put_string_chars(out,buffer);
  RETURN_IF_FAIL
  return(PL_unify(out,arg3));
}

void write_dot(environment * env, DdNode * bdd, FILE * file)
{
  const char * onames[]={"Out"};
  char ** inames;
  int i,b,index,nv;
  variable v;
  char numberVar[11],numberBit[11];
  inames= (char **) malloc(sizeof(char *)*(env->boolVars));
  index=0;
  for (i=0;i<env->nVars;i++)
  {
    v=env->vars[i];
      if (v.query)
        nv=v.nVal;
      else
        nv=v.nVal-1;
    for (b=0;b<nv;b++)
    {
      inames[b+index]=(char *) malloc(sizeof(char)*20);
      strcpy(inames[b+index],"X");
      sprintf(numberVar,"%d",i);
      strcat(inames[b+index],numberVar);
      strcat(inames[b+index],"_");
      sprintf(numberBit,"%d",b);
      strcat(inames[b+index],numberBit);
    }
    index=index+nv;
  }
  Cudd_DumpDot(env->mgr,1,&bdd,(const char * const *)inames,(const char * const *)onames,file);
  index=0;
  for (i=0;i<env->nVars;i++)
  {
    v=env->vars[i];
    if (v.query)
      nv=v.nVal;
    else
      nv=v.nVal-1;
    for (b=0;b<nv;b++)
    {
      free(inames[b+index]);
    }
    index=index+nv;
  }
  free(inames);
}

/*
static int rec_deref(void)
{
  YAP_Term arg1;
  DdNode * node;

  arg1=YAP_ARG1;
  node=(DdNode *) YAP_IntOfTerm(arg1);
  Cudd_RecursiveDeref(mgr_ex[ex], node);
  return 1;
}

*/

double ProbPath(example_data * ex_d,DdNode *node, int nex)
{
  int index,mVarIndex,pos,position;//,boolVarIndex;
  variable v;
  double res;
  double p,pt,pf,BChild0e,BChild1e,BChild0o,BChild1o,e0,e1;
  double *value_p, * value_p_e, *value_p_o,** eta_rule;
  DdNode *nodekey,*T,*F;

  // printf("node %p comp %d\n",node,comp );
  if (Cudd_IsConstant(node))
  {
    // printf("constant\n");
    return 1.0;
  }
  else
  {
    nodekey=Cudd_Regular(node);
    value_p=get_value(ex_d->nodesB,nodekey);
    if (value_p!=NULL)
    {
      // printf("found %f\n", *value_p);
      return *value_p;
    }
    else
    {
      index=Cudd_NodeReadIndex(node);
      p=ex_d->env[nex].probs[index];
      T = Cudd_T(node);
      F = Cudd_E(node);
      pf=ProbPath(ex_d,F,nex);
      pt=ProbPath(ex_d,T,nex);
      // printf("pt %f pf %f\n",pt,pf );
      if (Cudd_IsComplement(F))
        pf=1.0-pf;
      // printf("pt %f pf %f\n",pt,pf );

      BChild0e=pf*(1-p);
      BChild0o=(1-pf)*(1-p);
      BChild1e=pt*p;
      BChild1o=(1-pt)*p;
      value_p_e=get_value(ex_d->nodesFE,nodekey);
      value_p_o=get_value(ex_d->nodesFO,nodekey);
      e0 = (*value_p_e)*BChild0e+(*value_p_o)*BChild0o;
      e1 = (*value_p_e)*BChild1e+(*value_p_o)*BChild1o;
    //  printf("e node %p %f %f %f %f\n",node,*value_p_e,*value_p_o,e0,e1 );
      mVarIndex=ex_d->env[nex].bVar2mVar[index];
      v=ex_d->env[nex].vars[mVarIndex];
      pos=index-v.firstBoolVar;
      if (ex_d->tunable_rules[v.nRule])
      {
        eta_rule=ex_d->eta_temp[v.nRule];
        eta_rule[pos][0]=eta_rule[pos][0]+e0;
        eta_rule[pos][1]=eta_rule[pos][1]+e1;
      }
      res=BChild0e+BChild1e;
      add_node(ex_d->nodesB,nodekey,res);
      position=Cudd_ReadPerm(ex_d->env[nex].mgr,index);
      position=position+1;
//      boolVarIndex=Cudd_ReadInvPerm(ex_d->env[nex].mgr,position);//Returns the index of the variable currently in the i-th position of the order.
      if (position<ex_d->env[nex].boolVars)
      {
        ex_d->sigma[position]=ex_d->sigma[position]+e0+e1;
      }
      if(!Cudd_IsConstant(T))
      {
        index=Cudd_NodeReadIndex(T);
        position=Cudd_ReadPerm(ex_d->env[nex].mgr,index);
        ex_d->sigma[position]=ex_d->sigma[position]-e1;
      }

      if(!Cudd_IsConstant(F))
      {
        index=Cudd_NodeReadIndex(F);
        position=Cudd_ReadPerm(ex_d->env[nex].mgr,index);
        ex_d->sigma[position]=ex_d->sigma[position]-e0;
      }

      return res;
    }
  }
}




void Forward(example_data * ex_d,DdNode *root, int nex)
{
  DdNode *** nodesToVisit;
  int * NnodesToVisit,comp;
  double FrootE,FrootO;

  environment env;
  int i,j;
  env=ex_d->env[nex];
  comp=Cudd_IsComplement(root);
  if (comp)
  {
    FrootE=0.0;
    FrootO=1.0;
  }
  else
  {
    FrootE=1.0;
    FrootO=0.0;
  }
  add_node(ex_d->nodesFE,Cudd_Regular(root),FrootE);
  add_node(ex_d->nodesFO,Cudd_Regular(root),FrootO);
  if (env.boolVars)
  {
    nodesToVisit= (DdNode ***)malloc(sizeof(DdNode **)* env.boolVars);
    NnodesToVisit= (int *)malloc(sizeof(int)* env.boolVars);
    nodesToVisit[0]=(DdNode **)malloc(sizeof(DdNode *));
    nodesToVisit[0][0]=root;
    NnodesToVisit[0]=1;
    for(i=1;i<env.boolVars;i++)
    {
      nodesToVisit[i]=NULL;
      NnodesToVisit[i]=0;
    }
    for(i=0;i<env.boolVars;i++)
    {
      for(j=0;j<NnodesToVisit[i];j++)
      UpdateForward(ex_d,nodesToVisit[i][j],nex,nodesToVisit,NnodesToVisit);
    }
    for(i=0;i<env.boolVars;i++)
    {
      free(nodesToVisit[i]);
    }
    free(nodesToVisit);
    free(NnodesToVisit);
  }
}

void UpdateForward(example_data *ex_d,DdNode *node, int nex,
  DdNode *** nodesToVisit, int * NnodesToVisit)
{
  int index,position;
  DdNode *T,*E,*nodereg;
  double *value_p_E,*value_p_O,*value_p_T_E,*value_p_T_O,
    *value_p_F_E,*value_p_F_O,p,value_par_E,value_par_O;

// printf("F node %p comp %d\n",node,Cudd_IsComplement(node) );
  if (Cudd_IsConstant(node))
  {
    return;
  }
  else
  {
    index=Cudd_NodeReadIndex(node);
    p=ex_d->env[nex].probs[index];
    nodereg=Cudd_Regular(node);
    value_p_E=get_value(ex_d->nodesFE,nodereg);
    value_p_O=get_value(ex_d->nodesFO,nodereg);
    if (value_p_E== NULL)
    {
      printf("Error\n");
      return;
    }
    else
    {
      T = Cudd_T(node);
      E = Cudd_E(node);
      if (!Cudd_IsConstant(T))
      {
        value_p_T_E=get_value(ex_d->nodesFE,T);
        value_p_T_O=get_value(ex_d->nodesFO,T);
        if (value_p_T_E!= NULL)
        {
           *value_p_T_E= *value_p_T_E+*value_p_E*p;
           *value_p_T_O= *value_p_T_O+*value_p_O*p;
          // printf("update f t %p %f %f %f %f\n",T,*value_p_T_E,
          //  *value_p_E*p,*value_p_T_O,*value_p_O*p);
        }
        else
        {
          // printf("new f t %p %f %f \n",T,*value_p_E*p,*value_p_O*p );

          add_or_replace_node(ex_d->nodesFE,Cudd_Regular(T),*value_p_E*p);
          add_or_replace_node(ex_d->nodesFO,Cudd_Regular(T),*value_p_O*p);
          index=Cudd_NodeReadIndex(T);
          position=Cudd_ReadPerm(ex_d->env[nex].mgr,index);
          nodesToVisit[position]=(DdNode **)realloc(nodesToVisit[position],
	    (NnodesToVisit[position]+1)* sizeof(DdNode *));
          nodesToVisit[position][NnodesToVisit[position]]=T;
          NnodesToVisit[position]=NnodesToVisit[position]+1;
        }
      }
      if (!Cudd_IsConstant(E))
      {
        value_p_F_E=get_value(ex_d->nodesFE,Cudd_Regular(E));
        value_p_F_O=get_value(ex_d->nodesFO,Cudd_Regular(E));
        // if (Cudd_IsComplement(E))
        //   value_par=1 - *value_p;
        // else
        //   value_par= *value_p;
        // if (Cudd_IsComplement(E))
        //   p=1 -p;
        if (Cudd_IsComplement(E))
        {
          value_par_E= *value_p_O;
          value_par_O= *value_p_E;
        }
        else
        {
          value_par_E= *value_p_E;
          value_par_O= *value_p_O;
        }
        // printf("f child %d %f %f\n",Cudd_IsComplement(E),value_par_E,value_par_O );

        if (value_p_F_E!= NULL)
        {

          *value_p_F_E= *value_p_F_E+value_par_E*(1-p);
          *value_p_F_O= *value_p_F_O+value_par_O*(1-p);
          // printf("update f f %p %f %f %f %f\n",E,*value_p_F_E, value_par_E*(1-p),
        // *value_p_F_O, value_par_O*(1-p));
        }
        else
        {
                              // printf("new f f %p %f\n",E,value_par_E*(1-p) );

          add_or_replace_node(ex_d->nodesFE,Cudd_Regular(E),value_par_E*(1-p));
          add_or_replace_node(ex_d->nodesFO,Cudd_Regular(E),value_par_O*(1-p));
          index=Cudd_NodeReadIndex(E);
          position=Cudd_ReadPerm(ex_d->env[nex].mgr,index);
          nodesToVisit[position]=(DdNode **)realloc(nodesToVisit[position],
	    (NnodesToVisit[position]+1)* sizeof(DdNode *));
          nodesToVisit[position][NnodesToVisit[position]]=E;
          NnodesToVisit[position]=NnodesToVisit[position]+1;
        }
      }
      return;
    }
  }
}




double GetOutsideExpe(example_data * ex_d,DdNode *root,double ex_prob, int nex)
{
  int i,j,mVarIndex,bVarIndex,firstBoolVarOfRule,nRule;
  double **eta_rule;
  double theta,rootProb, T=0;


  ex_d->sigma=(double *)malloc(ex_d->env[nex].boolVars * sizeof(double));

  for (j=0; j<ex_d->env[nex].boolVars; j++)
  {
    ex_d->sigma[j]=0;
  }
  for (j=0; j<ex_d->nRules; j++)
  {
    if (ex_d->tunable_rules[j])
      for (i=0; i<ex_d->rules[j]-1; i++)
      {
        ex_d->eta_temp[j][i][0]=0;
        ex_d->eta_temp[j][i][1]=0;
      }
  }
  rootProb=ProbPath(ex_d,root,nex);
  if (Cudd_IsComplement(root))
    rootProb=1.0-rootProb;
  if (rootProb>0.0)
  {
    for (j=0; j<ex_d->env[nex].boolVars; j++)
    {
      T += ex_d->sigma[j];
      bVarIndex=Cudd_ReadInvPerm(ex_d->env[nex].mgr,j);
      if (bVarIndex==-1)
      {
        bVarIndex=j;
      }

      mVarIndex=ex_d->env[nex].bVar2mVar[bVarIndex];

      firstBoolVarOfRule=ex_d->env[nex].vars[mVarIndex].firstBoolVar;
      i=bVarIndex-firstBoolVarOfRule;
      theta=ex_d->env[nex].probs[bVarIndex];
      nRule=ex_d->env[nex].vars[mVarIndex].nRule;
      if (ex_d->tunable_rules[nRule])
      {
        eta_rule=ex_d->eta_temp[nRule];
        eta_rule[i][0]=eta_rule[i][0]+T*(1-theta);
        eta_rule[i][1]=eta_rule[i][1]+T*theta;
      }
    }

    for (j=0; j<ex_d->nRules; j++)
    {
      if (ex_d->tunable_rules[j])
        for (i=0; i<ex_d->rules[j]-1; i++)
        {
          ex_d->eta[j][i][0]=ex_d->eta[j][i][0]+
      ex_d->eta_temp[j][i][0]*ex_prob/rootProb;
          ex_d->eta[j][i][1]=ex_d->eta[j][i][1]+
      ex_d->eta_temp[j][i][1]*ex_prob/rootProb;
        }
    }
  }
  free(ex_d->sigma);
  return rootProb;
}


void Maximization(example_data * ex_d)
{
  int r,i,j,e;
  double sum=0;
  double *probs_rule,**eta_rule;

  for (r=0;r<ex_d->nRules;r++)
  {
    if (ex_d->tunable_rules[r])
    {
      eta_rule=ex_d->eta[r];
      for (i=0;i<ex_d->rules[r]-1;i++)
      {
        sum=(eta_rule[i][0]+eta_rule[i][1]);
        if (sum==0.0)
        {
          ex_d->arrayprob[r][i]=0;
        }
        else
          ex_d->arrayprob[r][i]=eta_rule[i][1]/sum;
      }
    }
  }

  for(e=0;e<ex_d->ex;e++)
  {
    for (j=0;j<ex_d->env[e].nVars;j++)
    {
      r=ex_d->env[e].vars[j].nRule;
      if (ex_d->tunable_rules[r])
      {
        probs_rule=ex_d->arrayprob[r];
        for(i=0;i<ex_d->rules[r]-1;i++)
        {
          ex_d->env[e].probs[ex_d->env[e].vars[j].firstBoolVar+i]=probs_rule[i];
        }
      }
    }
  }
}



static foreign_t init_par(example_data * ex_d, term_t ruleHeadsArg)
{
  double * theta,p0;
  double pmass,par;
  double **Theta_rules;
  double ***eta;
  double ***eta_temp;
  int ret,i,j,e,rule;
  term_t head=PL_new_term_ref();
  term_t p=PL_new_term_ref();
  term_t ruleHeadsTerm;
  size_t nHeads,nRules;
  int *rules, *tun_rules;

  ruleHeadsTerm=PL_copy_term_ref(ruleHeadsArg);
  ret=PL_skip_list(ruleHeadsTerm,0,&nRules);
  if (ret!=PL_LIST) return FALSE;

  ex_d->nRules=nRules;
  ex_d->rules= (int *) malloc(nRules * sizeof(int));
  rules=ex_d->rules;
  ex_d->tunable_rules= (int *) malloc(nRules * sizeof(int));
  tun_rules=ex_d->tunable_rules;
  ex_d->eta= (double ***) malloc(nRules * sizeof(double **));
  eta=ex_d->eta;
  ex_d->eta_temp= (double ***) malloc(nRules * sizeof(double **));
  eta_temp=ex_d->eta_temp;
  ex_d->nodes_probs=NULL;
  ex_d->arrayprob=(double **) malloc(nRules * sizeof(double *));

  Theta_rules=(double **)malloc(nRules *sizeof(double *));

  for (j=0;j<nRules;j++)
  {
    
    ret=PL_get_list(ruleHeadsTerm,head,ruleHeadsTerm);
    RETURN_IF_FAIL
    pmass=0;
    if (PL_is_list(head)) 
    { 
      ret=PL_skip_list(head,0,&nHeads);
      if (ret!=PL_LIST) return FALSE;
      if (nHeads==1) // fixed parameters
      {
        ret=PL_get_head(head,head);
        RETURN_IF_FAIL 
        ret=PL_skip_list(head,0,&nHeads);
        if (ret!=PL_LIST) return FALSE;
        tun_rules[j]=0;
      }
      else // initial parameters
        tun_rules[j]=1;
        
      Theta_rules[j]=(double *)malloc(nHeads*sizeof(double));
      theta=Theta_rules[j];
      rules[j]=nHeads,
      ex_d->arrayprob[j]= (double *) malloc((nHeads-1)*sizeof(double));
      eta[j]= (double **) malloc((nHeads-1)*sizeof(double *));
      eta_temp[j]= (double **) malloc((nHeads-1)*sizeof(double *));

      for (i=0;i<nHeads-1;i++)
      {
        ret=PL_get_list(head,p,head);
        RETURN_IF_FAIL
        ret=PL_get_float(p, &par);
        RETURN_IF_FAIL
        eta[j][i]=(double *) malloc(2*sizeof(double));
        eta_temp[j][i]=(double *) malloc(2*sizeof(double));
        pmass=pmass+par;
        theta[i]=par;
        ex_d->arrayprob[j][i]=par;
      }
      theta[nHeads-1]=1-pmass;
    }
    else
    {
      ret=PL_get_integer(head,&rules[j]);
      nHeads=rules[j];
      
      RETURN_IF_FAIL
      Theta_rules[j]=(double *)malloc(nHeads*sizeof(double));
      theta=Theta_rules[j];
      ex_d->arrayprob[j]= (double *) malloc((nHeads-1)*sizeof(double));
      
      eta[j]= (double **) malloc((nHeads-1)*sizeof(double *));
      eta_temp[j]= (double **) malloc((nHeads-1)*sizeof(double *));
      tun_rules[j]=1;
      for (i=0;i<rules[j]-1;i++)
      {
        eta[j][i]=(double *) malloc(2*sizeof(double));
        eta_temp[j][i]=(double *) malloc(2*sizeof(double));
      }
      if (ex_d->alpha==0.0)
      {
        for (i=0;i<rules[j]-1;i++)
        {
          par=uniform_sample()*(1-pmass);
          pmass=pmass+par;
          theta[i]=par;
          ex_d->arrayprob[j][i]=par;
        }
        theta[nHeads-1]=1-pmass;
      }
      else
      {
        symmetric_dirichlet_sample(ex_d->alpha,rules[j],theta);
        for (i=0;i<rules[j]-1;i++)
          ex_d->arrayprob[j][i]=theta[i];
      }
    }
  }

  for(e=0;e<ex_d->ex;e++)
  {
    for (j=0; j<ex_d->env[e].nVars; j++)
    {
      rule=ex_d->env[e].vars[j].nRule;
      theta=Theta_rules[rule];
      p0=1;
      for (i=0; i<ex_d->env[e].vars[j].nVal-1;i++)
      {
        ex_d->env[e].probs[ex_d->env[e].vars[j].firstBoolVar+i]=theta[i]/p0;
        p0=p0*(1-theta[i]/p0);
      }
    }
  }
  for (j=0;j<ex_d->nRules;j++)
  {
    free(Theta_rules[j]);
  }
  free(Theta_rules);
  return TRUE;
}
static foreign_t rand_seed(term_t arg1)
{
  int seed;
  int ret;

  ret=PL_get_integer(arg1,&seed);
  RETURN_IF_FAIL

  srand((unsigned)seed);

  PL_succeed;
}

static foreign_t EM(term_t arg1,term_t arg2,term_t arg3,term_t arg4,term_t arg5,
term_t arg6,term_t arg7,term_t arg8,term_t arg9)
{
  term_t pterm,nil,out1,out2,out3,nodesTerm,ruleTerm,tail,pair,compoundTerm;
  DdNode * node1,**nodes_ex;
  int r,i,iter,cycle,ret;
  long iter1;
  size_t lenNodes;
  example_data * ex_d;



  double CLL0= -2.2*pow(10,10); //-inf
  double CLL1= -1.7*pow(10,8);  //+inf
  double p,p0,**eta_rule,ea,er;
  double ratio,diff;

  term_t head=PL_new_term_ref();

  ret=PL_get_pointer(arg1,(void **)&ex_d);
  RETURN_IF_FAIL
  ret=init_par(ex_d,arg2);
  RETURN_IF_FAIL
  pair=PL_new_term_ref();
  nodesTerm=PL_copy_term_ref(arg3);

  ret=PL_skip_list(nodesTerm,0,&lenNodes);
  if (ret!=PL_LIST) return FALSE;

  out1=PL_new_term_ref();
  out2=PL_new_term_ref();
  out3=PL_new_term_ref();
  ruleTerm=PL_new_term_ref();
  tail=PL_new_term_ref();
  pterm=PL_new_term_ref();
  nil=PL_new_term_ref();
  compoundTerm=PL_new_term_ref();

  ret=PL_get_float(arg4,&ea);
  RETURN_IF_FAIL

  ret=PL_get_float(arg5,&er);
  RETURN_IF_FAIL
  ret=PL_get_integer(arg6,&iter);
  RETURN_IF_FAIL

  nodes_ex=(DdNode **)malloc(lenNodes*sizeof(DdNode*));
  ex_d->nodes_probs=(double *)malloc(lenNodes*sizeof(double));
  ex_d->example_prob=(double *)malloc(lenNodes*sizeof(double));

  for (i=0;i<lenNodes;i++)
  {
    ret=PL_get_list(nodesTerm,pair,nodesTerm);
    RETURN_IF_FAIL
    ret=PL_get_list(pair,head,pair);
    RETURN_IF_FAIL
    ret=PL_get_pointer(head,(void **)&node1);
    RETURN_IF_FAIL
    nodes_ex[i]=node1;
    ret=PL_get_list(pair,head,pair);
    RETURN_IF_FAIL
    ret=PL_get_float(head,&(ex_d->example_prob[i]));
    RETURN_IF_FAIL
  }
  diff=CLL1-CLL0;
  ratio=diff/fabs(CLL0);
  if (iter==-1)
    iter1= 2147000000;
  else iter1=iter;

  cycle=0;
  while  ( (diff>ea) && (ratio>er) && (cycle<iter1) )
  {
    cycle++;
    for (r=0;r<ex_d->nRules;r++)
    {
      if (ex_d->tunable_rules[r])
        for (i=0;i<ex_d->rules[r]-1;i++)
        {
          eta_rule=ex_d->eta[r];
          eta_rule[i][0]=0;
          eta_rule[i][1]=0;
        }
    }
    CLL0 = CLL1;
    CLL1 = Expectation(ex_d,nodes_ex,lenNodes);
    Maximization(ex_d);
    diff=CLL1-CLL0;
    ratio=diff/fabs(CLL0);
  }
  ret=PL_put_nil(out2);
  RETURN_IF_FAIL
  for (r=0; r<ex_d->nRules; r++)
  {
    ret=PL_put_nil(tail);
    RETURN_IF_FAIL
    p0=1;
    for (i=0;i<ex_d->rules[r]-1;i++)
    {
      p=ex_d->arrayprob[r][i]*p0;
      ret=PL_put_float(pterm,p);
      RETURN_IF_FAIL
      ret=PL_cons_list(tail,pterm,tail);
      RETURN_IF_FAIL
      p0=p0*(1-ex_d->arrayprob[r][i]);
    }
    ret=PL_put_float(pterm,p0);
    RETURN_IF_FAIL
    ret=PL_cons_list(tail,pterm,tail);
    RETURN_IF_FAIL
    ret=PL_put_integer(ruleTerm,r);
    RETURN_IF_FAIL
    ret=PL_put_nil(nil);
    RETURN_IF_FAIL
    ret=PL_cons_list(tail,tail,nil);
    RETURN_IF_FAIL
    ret=PL_cons_list(compoundTerm,ruleTerm,tail);
    RETURN_IF_FAIL
    ret=PL_cons_list(out2,compoundTerm,out2);
    RETURN_IF_FAIL
  }
  ret=PL_put_nil(out3);
  RETURN_IF_FAIL
  for (i=0;i<lenNodes;i++)
  {
    ret=PL_put_float(pterm,ex_d->nodes_probs[i]);
    RETURN_IF_FAIL
    ret=PL_cons_list(out3,pterm,out3);
    RETURN_IF_FAIL
  }
  ret=PL_unify(out3,arg9);
  RETURN_IF_FAIL

  ret=PL_put_float(out1,CLL1);
  RETURN_IF_FAIL
  ret=PL_unify(out1,arg7);
  RETURN_IF_FAIL
  free(nodes_ex);
  free(ex_d->example_prob);
  free(ex_d->nodes_probs);

  return (PL_unify(out2,arg8));
}


/*

static int paths_to_non_zero(void)
{
  double paths;
  YAP_Term arg1,arg2,out;
  DdNode * node;

  arg1=YAP_ARG1;
  arg2=YAP_ARG2;
  node=(DdNode *)YAP_IntOfTerm(arg1);
  paths=Cudd_CountPathsToNonZero(node);
  out=YAP_MkFloatTerm(paths);
  return(YAP_Unify(out,arg2));
}

static int paths(void)
{
  double paths;
  YAP_Term arg1,arg2,out;
  DdNode * node;

  arg1=YAP_ARG1;
  arg2=YAP_ARG2;
  node=(DdNode *)YAP_IntOfTerm(arg1);
  paths=Cudd_CountPath(node);
  out=YAP_MkFloatTerm(paths);
  return(YAP_Unify(out,arg2));
}

static int dag_size(void)
{
  int size;
  YAP_Term arg1,arg2,out;
  DdNode * node;

  arg1=YAP_ARG1;
  arg2=YAP_ARG2;
  node=(DdNode *)YAP_IntOfTerm(arg1);
  size=Cudd_DagSize(node);
  out=YAP_MkIntTerm(size);
  return(YAP_Unify(out,arg2));
}
*/

FILE * open_file(char *filename, const char *mode)
/* opens a file */
{
  FILE *fp;

  if ((fp = fopen(filename, mode)) == NULL)
  {
    perror(filename);
    exit(1);
  }
  return fp;
}


tablerow* init_table(int varcnt) {
  int i;
  tablerow *tab;

  tab = (tablerow *) malloc(sizeof(rowel) * varcnt);
  for (i = 0; i < varcnt; i++)
  {
    tab[i].row = NULL;
    tab[i].cnt = 0;
  }
  return tab;
}


void add_node(tablerow *tab, DdNode *node, double value) {
  int index = Cudd_NodeReadIndex(node);

  tab[index].row = (rowel *) realloc(tab[index].row,
    (tab[index].cnt + 1) * sizeof(rowel));
  tab[index].row[tab[index].cnt].key = node;
  tab[index].row[tab[index].cnt].value = value;
  tab[index].cnt += 1;
}

void add_or_replace_node(tablerow *tab, DdNode *node, double value)
{
  int i;
  int index = Cudd_NodeReadIndex(node);
  for(i = 0; i < tab[index].cnt; i++)
  {
    if (tab[index].row[i].key == node)
    {
      tab[index].row[i].value=value;
      return;
    }
  }
  tab[index].row = (rowel *) realloc(tab[index].row,
    (tab[index].cnt + 1) * sizeof(rowel));
  tab[index].row[tab[index].cnt].key = node;
  tab[index].row[tab[index].cnt].value = value;
  tab[index].cnt += 1;
}

double * get_value(tablerow *tab,  DdNode *node) {
  int i;
  int index = Cudd_NodeReadIndex(node);

  for(i = 0; i < tab[index].cnt; i++)
  {
    if (tab[index].row[i].key == node)
    {
      return &tab[index].row[i].value;
    }
  }
  return NULL;
}

void destroy_table(tablerow *tab,int varcnt)
{
  int i;

  for (i = 0; i < varcnt; i++)
  {
    free(tab[i].row);
  }
  free(tab);
}

expltablerow* expl_init_table(int varcnt) {
  int i;
  expltablerow *tab;

  tab = (expltablerow *) malloc(sizeof(explrowel) * varcnt);
  for (i = 0; i < varcnt; i++)
  {
    tab[i].row = NULL;
    tab[i].cnt = 0;
  }
  return tab;
}


void expl_add_node(expltablerow *tab, DdNode *node, int comp, prob_abd_expl value) {
  int index = Cudd_NodeReadIndex(node);

  tab[index].row = (explrowel *) realloc(tab[index].row,
    (tab[index].cnt + 1) * sizeof(explrowel));
  tab[index].row[tab[index].cnt].key.node = node;
  tab[index].row[tab[index].cnt].key.comp = comp;
  tab[index].row[tab[index].cnt].value = value;
  tab[index].cnt += 1;
}

// try to reuse
DdNode* get_node(DdNode *node, tablerow *tab) {
  int index = Cudd_NodeReadIndex(node);
  int i;

  for(i = 0; i < tab[index].cnt; i++) {
    if(tab[index].row[i].key == node) {
      return tab[index].row[i].key;
    }
  }
  return NULL;
}

prob_abd_expl * expl_get_value(expltablerow *tab,  DdNode *node, int comp) {
  int i;
  int index = Cudd_NodeReadIndex(node);

  for(i = 0; i < tab[index].cnt; i++)
  {
    if (tab[index].row[i].key.node == node &&
       tab[index].row[i].key.comp == comp)
    {
      return &tab[index].row[i].value;
    }
  }
  return NULL;
}

void expl_destroy_table(expltablerow *tab,int varcnt)
{
  int i,j;

  for (i = 0; i < varcnt; i++)
  {
    for (j = 0; j< tab[i].cnt; j++)
    {
      free_list(tab[i].row[j].value.mpa);
    }
    free(tab[i].row);
  }
  free(tab);
}

// debugging functions

void print_abd_explan(explan_t *et) {
  explan_t *current_explan = et;
  while(current_explan != NULL) {
    printf("assign var: %d\nassign val: %d\n",current_explan->a.var,current_explan->a.val);
    current_explan = current_explan->next;
  }
}

void print_prob_abd_expl(prob_abd_expl *pae) {
  printf("prob: %lf\nExplan:\n",pae->prob);
  print_abd_explan(pae->mpa);
}

// prints all the fields of a variable data structure
void dump_var(variable *var) {
  printf("\t\tnVal: %d\n", var->nVal);
  printf("\t\tnRule: %d\n", var->nRule);
  printf("\t\tfirstBoolVar: %d\n", var->firstBoolVar);
  printf("\t\tabducible: %d\n", var->abducible);
  printf("\t\tquery: %d\n", var->query);
  printf("\t\tdecision: %d\n", var->decision);
  printf("\t\toptimizable: %d\n", var->optimize);
}

// prints all the variables of the environment
void dump_env(environment *env) {
  int i;

  printf("n_abd_boolVars: %d\n",env->n_abd_boolVars);
  printf("n_opt_boolVars: %d\n",env->n_opt_boolVars);
  printf("n_abd: %d\n",env->n_abd);
  printf("n_opt: %d\n",env->n_opt);

  printf("nVars: %d\n",env->nVars);
  for(i = 0; i < env->nVars; i++) {
    printf("\tvars[%d]: \n",i);
    dump_var(&env->vars[i]);
  }

  printf("boolVars: %d\n",env->boolVars);
  for(i = 0; i < env->boolVars; i++) {
    printf("\tbVar2mVar[%d] = %d\n",i,env->bVar2mVar[i]);
    printf("\tprobs[%d] = %lf\n",i,env->probs[i]);
  }

  printf("nRules: %d\n",env->nRules);
  for(i = 0; i < env->nRules; i++) {
    printf("\trules[%d] = %d\n",i,env->bVar2mVar[i]);
  }
}

// prints CUDD venv variables
void debug_cudd_env(environment *env, int i) {
  printf("----- %d -----\n",i);
  printf("Dead nodes (Cudd_ReadDead): %d\n",Cudd_ReadDead(env->mgr));
  printf("Cudd check zero ref (node with non 0 ref, Cudd_CheckZeroRef): %d\n",Cudd_CheckZeroRef(env->mgr));
  printf("Cudd check keys (Cudd_CheckKeys): %d\n",Cudd_CheckKeys(env->mgr));
  printf("Cudd debug check (Cudd_DebugCheck): %d\n",Cudd_DebugCheck(env->mgr));
  printf("Cudd_ReadMaxMemory: %lu\n",Cudd_ReadMaxMemory(env->mgr));
  printf("DdManager vars: %d | ", Cudd_ReadSize(env->mgr)); /*Returns the number of BDD variables in existence*/
  printf("DdManager nodes: %ld | ", Cudd_ReadNodeCount(env->mgr)); /*Reports the number of live nodes in BDDs and ADDs*/
  printf("DdManager reorderings: %d | ", Cudd_ReadReorderings(env->mgr) ); /*Returns the number of times reordering has occurred*/
  printf("DdManager memory: %ld |\n\n", Cudd_ReadMemoryInUse(env->mgr) ); /*Returns the memory in use by the manager measured in bytes*/
  printf("-------------\n");
}

// predicate equivalent to debug_cudd_env
// out_null is empty, here just in case it's needed
static foreign_t debug_cudd_var(term_t env_ref, term_t out_null) {
  int ret;
  term_t out;
  environment *env;

  ret = PL_get_pointer(env_ref,(void **)&env);
  RETURN_IF_FAIL
  printf("----- DEBUG CUDD -----\n");
  printf("Dead nodes (Cudd_ReadDead): %d\n",Cudd_ReadDead(env->mgr));
  printf("Cudd check zero ref (node with non 0 ref, Cudd_CheckZeroRef): %d\n",Cudd_CheckZeroRef(env->mgr));
  printf("Cudd check keys (Cudd_CheckKeys): %d\n",Cudd_CheckKeys(env->mgr));
  printf("Cudd debug check (Cudd_DebugCheck): %d\n",Cudd_DebugCheck(env->mgr));
  printf("----- END DEBUG CUDD -----\n");
  out = PL_new_term_ref();
  ret = PL_put_nil(out);
  RETURN_IF_FAIL
  return(PL_unify(out,out_null));
}



// ======================
// JUSTIFICATION MANAGEMENT
// RICCARDO
static foreign_t ret_justs_bdd(term_t,term_t,term_t,term_t,term_t);

// RICCARDO: questa è la parte aggiunta
computed_justs_table* init_justs_table(int varcnt) {
  int i;
  computed_justs_table *tab;

  tab = (computed_justs_table *) malloc(sizeof(computed_justs_table_el) * varcnt);
  for (i = 0; i < varcnt; i++)
  {
    tab[i].row = NULL;
    tab[i].n_nodes = 0;
  }
  return tab;
}

// questa funzione aggiunge nella tabella il nodo con la justs_table a lui associata
void add_node_justs_table(computed_justs_table *tab, DdNode *node, justs_table value) {
  int index = Cudd_NodeReadIndex(node);

  tab[index].row = (computed_justs_table_el *) realloc(tab[index].row,
    (tab[index].n_nodes + 1) * sizeof(computed_justs_table_el));
  tab[index].row[tab[index].n_nodes].key = node;
  tab[index].row[tab[index].n_nodes].value = value;
  tab[index].n_nodes += 1;
}

void add_or_replace_node_justs_table(computed_justs_table *tab, DdNode *node, justs_table value)
{
  int i;
  int index = Cudd_NodeReadIndex(node);
  for(i = 0; i < tab[index].n_nodes; i++)
  {
    if (tab[index].row[i].key == node)
    {
      tab[index].row[i].value=value;
      return;
    }
  }
  tab[index].row = (computed_justs_table_el *) realloc(tab[index].row,
    (tab[index].n_nodes + 1) * sizeof(computed_justs_table_el));
  tab[index].row[tab[index].n_nodes].key = node;
  tab[index].row[tab[index].n_nodes].value = value;
  tab[index].n_nodes += 1;
}

// RICCARDO questa funzione cerca nella tabella il nodo voluto, non guarda l'indice della variabile ma il noto in sé
// restituisce NULL se non c'è il nodo o il puntatore alla paths_table se il nodo è in tabella
justs_table * get_value_justs_table(computed_justs_table *tab,  DdNode *node) {
  int i;
  int index = Cudd_NodeReadIndex(node);

  for(i = 0; i < tab[index].n_nodes; i++)
  {
    if (tab[index].row[i].key == node)
    {
      return &tab[index].row[i].value;
    }
  }
  return NULL;
}

void destroy_justs_table(computed_justs_table *tab,int varcnt)
{
  int i;

  for (i = 0; i < varcnt; i++)
  {
    free(tab[i].row);
  }
  free(tab);
}

// returns 1 if array1 must be kept (array1 is subset of array2),
//         2 if array2 must be kept (array2 is subset of array1),
//         0 if both arrays must be kept
int just_intersection(int *a, int *b, int n, int m)
{
  int i = 0, j = 0, count = 0;

  // printf("just_intersection - coumt: %d -- n: %d -- m: %d\n",count,n,m);
  while (i < n && j < m) {
    // printf("just_intersection - coumt: %d -- n: %d -- m: %d\n",count,n,m);
    // printf("just_intersection - a[i]: %d -- i: %d -- b[j]: %d -- j: %d\n",a[i],i,b[j],j);
    if (a[i] < b[j]) {
      j++;
    }
    else if (b[j] < a[i]) {
      i++;
    }
    else {
          
      // when both are equal
      count++;
      i++;
      j++;
    }
  }
  // printf("just_intersection - coumt: %d -- n: %d -- m: %d\n",count,n,m);
  if (count == n) {
    return 1;
  } else if (count == m) {
    return 2;
  } else return 0;

}

void print_justs_table(justs_table justs_tab) {
  printf("-- JUSTS TABLE --\n");
  int i, k;
  printf("justs_tab.n_justs: %d\n",justs_tab.n_justs);
  for (i = 0; i < justs_tab.n_justs; i++) {
    printf("%i: n_nodes: %d, prob: %lf\n - ",i, justs_tab.justs_list[i].n_nodes,justs_tab.justs_list[i].prob);
    for (k = 0; k < justs_tab.justs_list[i].n_nodes; k++) {
      printf("%d ", justs_tab.justs_list[i].nodes[k]);
    }
    printf("\n");
  }
  printf("-- END JUSTS TABLE --\n");
}

// questa funzione è la versione modificata di get_paths_rec
/*
La funzione prende un BDD e ne ricava l'insieme di spiegazioni (justification)
*/
justs_table get_justs_rec(environment *env, DdNode *node, int comp_par, computed_justs_table *cpt) {
  // DdNode *node = Cudd_Regular(n);
  
  // RICCARDO Aggiunto nodekey
  DdNode *nodekey, *T, *F;
  justs_table computed_just;
  justs_table computed_true, computed_false;
  justs_table *value_p;
  int i,j,k,comp;
  int size_to_compare;
  int which_keep;

  // printf("node: %d  --  %d\n",Cudd_NodeReadIndex(node),node);

  comp = Cudd_IsComplement(node);
  comp = (comp && !comp_par) ||(!comp && comp_par);

  computed_just.n_justs = 0;
  // computed_just.justs_list = NULL;

  if(Cudd_IsConstant(node)) {
    //printf("constant\n");
    computed_just.n_justs = 1;
    computed_just.justs_list = malloc(sizeof(just));
    if(comp) {
      computed_just.justs_list[0].prob = 0;
    }
    else {
      computed_just.justs_list[0].prob = 1;
    }
    computed_just.justs_list[0].nodes = NULL; 
    computed_just.justs_list[0].n_nodes = 0; 
  }  else {

    /*
    Arrivati a questo punto, il il nodo attuale (NA) è già stato calcolato, si trova in table, e quindi può essere direttamente restituito, altrimenti
    serve costruire per il nodo attuale (NA) le justification (spiegazioni minime).Per farlo deve recuperare i percorso (paths) dal nodo positivo (NP) e da quello negativo (NN). 
    Tali percorsi devono essere calcolati, scorrendo il BDD nei nodi inferiori. In questo caso ottengo due tabelle contenenti i path dai due nodi NP e NN.
    Questi, a loro volta possono provenire da table oppure essere costruiti ricorsivamente.
    La costruzione ricorsiva partirà sempre dalla foglia a salire, quindi il primo step sarà arrivare alla foglia, in quel caso se NP e NN sono foglie, la tabella avrà un solo 
    percorso con il nodo considerato -> caso base.
    ??: Cosa succede se un nodo ha NP a 1 e NN a qualcos'altro? !!: size_to_compare = 0, non si entra nel ciclo e si inserisce direttamente grazie all if(which_keep==0).
    Salendo, si arriva al generico NA (nodo attuale), che riceverà due tabelle generiche da NP e NA. Entrambe avranno solo percorsi minimi, quindi prendo i percorsi positivi, aggiungo il nodo
    attuale e li salvo per NA. A questo punto controllo i percorsi di NN. Per ogni percorso di NN possono succedere tre cose:
    1. esiste in NA un percorso proveniente da NP che è sottoinsieme del percorso NN. A questo punto posso smettere di controllare, il percorso NN non verrà aggiunto a NA. Posso passare al successivo path NN.
    2. il percorso NN non è sottoinsieme di alcun percorso in NA e viceversa. In questo caso va aggiunto il eprcorso NN
    3. il percorso NN è sottoinsieme di un percorso in NA, quindi deve sostituire tale percorso.

    Per risolvere i punti 2 e 3 si mantengono 3 limiti, n_paths e size_to_compare, e un indice, k: n_paths dice quanti percorsi sono inseriti nel nodo NA (sia negativi che positivi), 
    size_to_compare dice quanti percorsi NP sono attualmente in NA, k serve per scorrere i percorsi provenienti da NP in NA per confrontarli con i percorsi provenienti da NN.
    Inizialmente, size_to_compare è pari a n_paths, perchè vengono inseriti in NA tutti i percorsi NP (che sono già minimali e quindi non devono essere controllati tra loro).
    Per ogni paths in NN, PNN, lo confronto con i path provenienti da NP contenuti in NA, quindi k scorrerà tra 0 e size_to_compare. Nel caso (2), PNN non ha nessuna relazione con alcun path in NA,
    quindi aggiungo PNN in coda all'array dei path di NA e aumento n_path (non size_to_compare perchè questo mi punta all'ultima posizione che contiene un path proveniente da NP).
    Nel caso (3), devo sostiture in path in NA (che proveniva da NP, poichè tutti i path di NN sono già minimali tra loro). In questo caso, per assicurare che i successivi path 
    di NN vengano confrontati SOLO con quelli provenienti da NP, decremento size_to_compare, perchè eliminerò un path di NP per fare posto a PNN, prendo il path in posizione size_to_compare,
    l'ultimo proveniente da NP e lo copio in posizione k, cioè al posto del path che deve essere sostituito da PNN (soprainsieme di PNN). Infine, copio PNN in posizione size_to_compare, senza
    aumentare n_path.
    In questo modo, sono sicuro che k <= size_to_compare perchè tutti i path provenienti da NP sono nelle prime posizioni e che i path da NN iniziano dalla posizione size_to_compare.
    ??: cosa succede se k=size_to_compare? !!: in questo caso non avviene la copia del path in posizione size_to_compare nella posizione k perchè è esso stesso quello che deve essere sostituito da PNN.
    */

    // RICCARDO qua ho tolto l'if seguente: if (Cudd_ReadPerm(env->mgr,Cudd_NodeReadIndex(node)) >= env->n_abd_boolVars)
    // RICCARDO subito sotto vado a recuperare il nodo specifico nella tabella
    nodekey=Cudd_Regular(node);
    value_p=get_value_justs_table(cpt,nodekey);

    // RICCARDO se trovo la justs_table la uso, altrimenti entro nei figli
    if(value_p!=NULL) {
      // check if the path is in the table
      // printf("Found\n");
      computed_just = *value_p;
      // print_justs_table(computed_just);
    } else {


      
      // RICCARDO  qua dovrebbe essere tutto uguale a get_paths_rec a parte diverse stampe
      // printf("enter in node \n");

      T = Cudd_T(node);
      F = Cudd_E(node);

      if(Cudd_IsComplement(node)) {
        T = Cudd_Not(T);
        F = Cudd_Not(F);
      }
      // printf("  TRUE\n");
      computed_true = get_justs_rec(env,T,comp,cpt);
      // printf("  FALSE\n");
      computed_false = get_justs_rec(env, F, comp,cpt);
      // computed_true should not contain deletable paths because it is either already built (so already checked) or built following a path
      // in the path, duplicated or deletable just should come only from positive/negative paths combined

      // printf("True\n");
      // print_justs_table(computed_true);
      // printf("False\n");
      // print_justs_table(computed_false);

      // printf("computed_true.n_paths: %d\n",computed_true.n_paths);
      computed_just.justs_list = malloc(sizeof(just)*(computed_true.n_justs + computed_false.n_justs));
      
      // computed_just.justs_list[0].n_nodes = 0;
      // computed_just.justs_list[0].nodes = NULL;
      for(i = 0; i < computed_true.n_justs; i++) {
        if(computed_true.justs_list[i].prob != 0) {
          // copy all the justs in the current list and add the current
          // printf("true: computed_true.justs_list[i].n_nodes: %d, computed_true.n_justs: %d\n",computed_true.justs_list[i].n_nodes,computed_true.n_justs);
          // copy of all computed_true.just
          j = computed_true.justs_list[i].n_nodes;
          // computed_just.justs_list[i].nodes = malloc(sizeof(couple) * (computed_true.justs_list[i].n_nodes + 1)); // for the current node
          computed_just.justs_list[i].nodes = malloc(sizeof(int) * (j + 1));
          for(j = 0; j < computed_true.justs_list[i].n_nodes; j++) {
            // printf("copy\n");
            computed_just.justs_list[i].nodes[j] = computed_true.justs_list[i].nodes[j];
          }
          
          // add current node
          
          // computed_just.justs_list[i].nodes = realloc(computed_just.justs_list[i].nodes,sizeof(couple)*(j+1));
          computed_just.justs_list[i].nodes[j] = Cudd_NodeReadIndex(node);

          computed_just.justs_list[i].n_nodes = j + 1;
          double p = env->probs[Cudd_NodeReadIndex(node)];
          computed_just.justs_list[i].prob = computed_true.justs_list[i].prob * p;

          computed_just.n_justs++;

          // print_justs_table(computed_just);
        }
      }

      // do the same for else
      size_to_compare = computed_just.n_justs;
      which_keep = 0;
      // computed_just.justs_list = realloc(computed_just.justs_list,sizeof(just)*(computed_false.n_justs + computed_true.n_justs));

      // printf("enter in computed_false\n");
      
      for(i = 0; i < computed_false.n_justs; i++) {
        if(computed_false.justs_list[i].prob != 0) {
          // copy all the justs in the current list and add the current
          // with mode 0
          // printf("false: %d\n",computed_false.n_justs);
          // printf("------------\nsize_to_compare: %d -- n_justs: %d -- entering in k loop\n", size_to_compare, computed_just.n_justs);
          for (k=0; k < size_to_compare; k++) {

           //  printf("i: %d -- k: %d\n",i,k);
            which_keep = just_intersection(computed_just.justs_list[k].nodes,
                          computed_false.justs_list[i].nodes,
                          computed_just.justs_list[k].n_nodes,
                          computed_false.justs_list[i].n_nodes);
            // returns 1 if array1 must be kept (array1 is subset of array2),
            //         2 if array2 must be kept (array2 is subset of array1),
            //         0 if both arrays must be kept

            // printf("which_keep: %d\n", which_keep);
            if (which_keep == 1) {
              // element from computed_false is superset of element of computed_true, no need to chek the others
              // free(computed_false.justs_list[i].nodes); // forse da togliere per fare più veloce
              break;
            } else if (which_keep == 2) {
              // remove from computed_true by moving the last to this position and reducing size_to_compare
              size_to_compare--;
              if (k < size_to_compare) {
                /*
                // computed_just.justs_list[computed_just.n_justs - 1].nodes = malloc(sizeof(couple) * (computed_false.justs_list[i].n_nodes + 1));
                computed_just.justs_list[k].nodes = realloc(computed_just.justs_list[k].nodes,sizeof(couple) * Cudd_ReadSize(env->mgr));
                for(j = 0; j < computed_just.justs_list[size_to_compare].n_nodes; j++) {
                  // copio tutti i nodi
                  computed_just.justs_list[k].nodes[j] = computed_just.justs_list[size_to_compare].nodes[j];
                }
                computed_just.justs_list[k].n_nodes = j; // RICCARDO  qua manca un +1
                computed_just.justs_list[k].prob = computed_just.justs_list[size_to_compare].prob;
                */
                
                free(computed_just.justs_list[k].nodes);
                computed_just.justs_list[k] = computed_just.justs_list[size_to_compare];
              }
              // copy element from computed_false. No need to increase computed_just.n_justs
              /*
              // computed_just.justs_list[computed_just.n_justs - 1].nodes = malloc(sizeof(couple) * (computed_false.justs_list[i].n_nodes + 1));
              computed_just.justs_list[size_to_compare].nodes = realloc(computed_just.justs_list[size_to_compare].nodes,sizeof(couple) * Cudd_ReadSize(env->mgr));
              for(j = 0; j < computed_false.justs_list[i].n_nodes; j++) {
                // copio tutti i nodi
                computed_just.justs_list[size_to_compare].nodes[j] = computed_false.justs_list[i].nodes[j];
              }
              // add current node
              // computed_just.justs_list[computed_just.n_justs - 1].nodes = realloc(computed_just.justs_list[computed_just.n_justs - 1].nodes, sizeof(couple) * (j + 1));
              // RICCARDO qua ho commentato le due righe sotto per non salvare nel just i rami negativi, se avrai queste due righe non commentate e aggiungere +1 sotto
              // computed_just.justs_list[computed_just.n_justs].nodes[j] = Cudd_NodeReadIndex(node);

              computed_just.justs_list[size_to_compare].n_nodes = j; // RICCARDO  qua manca un +1
              computed_just.justs_list[size_to_compare].prob = computed_false.justs_list[i].prob;
              */
              computed_just.justs_list[size_to_compare] = computed_false.justs_list[i];
              break;
            } // else which_keep == 0 -> continue the loop
          }

          if (which_keep == 0) {
            // it means that no changes have been done into computed_true -> must add at the end the new just
            // computed_just.justs_list[computed_just.n_justs - 1].nodes = malloc(sizeof(couple) * (computed_false.justs_list[i].n_nodes + 1));
            /*
            j = computed_false.justs_list[i].n_nodes;
            computed_just.justs_list[computed_just.n_justs].nodes = malloc(sizeof(int) * (j));
            for(j = 0; j < computed_false.justs_list[i].n_nodes; j++) {
              // copio tutti i nodi
              computed_just.justs_list[computed_just.n_justs].nodes[j] = computed_false.justs_list[i].nodes[j];
            }
            // add current node
            // computed_just.justs_list[computed_just.n_justs - 1].nodes = realloc(computed_just.justs_list[computed_just.n_justs - 1].nodes, sizeof(couple) * (j + 1));
            // RICCARDO qua ho commentato le due righe sotto per non salvare nel just i rami negativi, se avrai queste due righe non commentate e aggiungere +1 sotto
            // computed_just.justs_list[computed_just.n_justs].nodes[j] = Cudd_NodeReadIndex(node);

            computed_just.justs_list[computed_just.n_justs].n_nodes = j; // RICCARDO  qua manca un +1
            computed_just.justs_list[computed_just.n_justs].prob = computed_false.justs_list[i].prob;
            */
            computed_just.justs_list[computed_just.n_justs] = computed_false.justs_list[i];
            computed_just.n_justs++;
          }

          // print_justs_table(computed_just);
          // printf("------------\nsize_to_compare: %d -- n_justs: %d -- continue next just\n", size_to_compare, computed_just.n_justs);

        }
      }
      
      computed_just.justs_list = realloc(computed_just.justs_list, sizeof(just)*(computed_just.n_justs));

      // printf("computed_just.n_justs: %d\n", computed_just.n_justs);
      // print_justs_table(computed_just);
    
      // add the just to the table
      computed_just.comp = comp;
      //if(!Cudd_IsConstant(node)) {
      //  cpt->tables[Cudd_NodeReadIndex(node)] = computed_just;
      //}
      // RICCARDO qua aggiungo nella tableaa il justs_table con la nuova funzione
      add_node_justs_table(cpt,nodekey,computed_just);
    }
  }
  // printf("return %d\n\n",Cudd_NodeReadIndex(node));

  // printf("computed_just.n_justs: %d\n",computed_just.n_justs);

  return computed_just;
}

justs_table retrieve_justs_from_bdd(environment *env, DdNode *root) {
  int i;
  justs_table all_justs_list;
  computed_justs_table * cpt; // to store already computed paths
  // tablerow * table;

  i = Cudd_ReadSize(env->mgr);
  
  cpt = init_justs_table(i); // maybe env size?

  // printf("caller constant: %d\n",Cudd_IsConstant(root));
  all_justs_list = get_justs_rec(env,root,0,cpt);

  destroy_justs_table(cpt,i);
  // free(cpt.tables);

  return all_justs_list;
}

// RICCARDO fine parte aggiunta

// 1 0 -> [1,0]
// 3 2 not 1 0 -> [3,2,0]
// 3 2 not 0 -> [3,2]
// generates only the paths
// RICCARDO piccole modifiche qua per non stampare i not
term_t generate_prolog_just_list(justs_table *table) {
  int i, j, ret;
  term_t out, out_in, var, prob_term,just_term;
  functor_t minus;
  out = PL_new_term_ref();
  minus=PL_new_functor(PL_new_atom("-"), 2);
  prob_term = PL_new_term_ref();
  just_term = PL_new_term_ref();

  PL_put_nil(out);

  for(i = 0; i < table->n_justs; i++) {
    out_in = PL_new_term_ref();
    PL_put_nil(out_in);

    for(j = 0; j < table->justs_list[i].n_nodes; j++) {
      var = PL_new_term_ref();
      
      ret = PL_put_integer(var,table->justs_list[i].nodes[j]);
      RETURN_IF_FAIL
      
      ret = PL_cons_list(out_in,var,out_in);
      RETURN_IF_FAIL
    }

    assert(PL_put_float(prob_term,table->justs_list[i].prob));
    assert(PL_cons_functor(just_term, minus,out_in,prob_term));

    ret = PL_cons_list(out,just_term,out);
    RETURN_IF_FAIL
  }

  return out;
}

// converts a list of path (0,1) into an equation
// of the form x+y...
char *from_justs_to_sym_eq(justs_table *table, environment *env, all_data *opt_data, int *malloc_size) {
  int i, j, k, index;
  char *result = malloc(1);

  int size = 1;
  result[0] = '\0';
 
  // dump_env(env);
  // printf("n justs: %d\n",table->n_justs);
  for(i = 0; i < table->n_justs; i++) {
    // printf("current: %d\n",i);
    // printf("table->justs_list[i].n_nodes %d\n",table->justs_list[i].n_nodes);
    for(j = 0; j < table->justs_list[i].n_nodes; j++) {
      index = table->justs_list[i].nodes[j];
      // printf("index %d - %d\n",index,env->nVars);
      if(env->vars[index].optimize == 1) {
        // extract name
        for(k = 0; k < opt_data->n_triples; k++) {
          // printf("opt_data->triple[k].index_bdd %d \n",opt_data->triple[k].index_bdd);
          if(opt_data->triple[k].index_bdd == env->vars[index].nRule) {
            // extract the name
            size = size + strlen(opt_data->triple[k].name) + 1;
            result = realloc(result, size); // 1 is *
            snprintf(result + strlen(result), size, "%s*",opt_data->triple[k].name);
            // printf("%s*",opt_data->triple[k].name);
            break;
          }
        }
      }
      else {
        // printf("prob\n");
        // extract prob env->probs[index];
        size = size + 7;
        result = realloc(result, size); // 6 is 0.4lf
        snprintf(result + strlen(result), size, "%.4lf*", env->probs[index]);
      }
    }
    size = size + 7;
    result = realloc(result, size);
    snprintf(result + strlen(result), size, "%.4lf+", table->justs_list[i].prob);
  }

  result[strlen(result) - 1] = '\0'; // eat the extra +
  *malloc_size = size;
  return result;
}

// RICCARDO piccole modifiche qua per richiamare le mie funzioni
// eq_or_list takes values 1 for the symbolic equation (TRILLP) or 0 (or every other value) for a list (TRILL)
static foreign_t ret_justs_bdd(term_t env_ref, term_t root,term_t index_name, term_t eq_or_list, term_t symb_eq_out) {
  environment *env;
  DdNode *node;
  justs_table pt_test;
  term_t head, head2, out;
  term_t index_name_list; // lista che contiene associazione indice-nome-probabilità
  size_t n_index_names, len_line;
  all_data opt_data;

  double *probs_list = NULL;
  char *symbolic_path = NULL;
  char *str_tmp; // usata nella lettura di stringhe
  int eol;

  int i;
  int malloc_size;

  functor_t minus;
  minus=PL_new_functor(PL_new_atom("-"), 2);

  head = PL_new_term_ref();
  head2 = PL_new_term_ref();
  out = PL_new_term_ref();

  setlocale(LC_NUMERIC, "en_US.UTF-8"); // to have . instead of , for float

  assert(PL_get_pointer(env_ref,(void **)&env));
  assert(PL_get_pointer(root,(void **)&node));
  assert(PL_get_integer(eq_or_list,&eol));

  index_name_list = PL_copy_term_ref(index_name);
  assert(PL_skip_list(index_name_list,0,&n_index_names) && "PL_skip_list index_names_list error");

  // lista per le probabiltà
  probs_list = malloc(sizeof(double) * n_index_names); 
  
  // uso per poter riciclare le funzioni
  opt_data.triple = malloc(sizeof(name_indexes) * n_index_names);
  opt_data.n_triples = n_index_names;

  // leggo lista di elementi [indice,nome,prob]
  for (i = 0; i < n_index_names; i++)   {
    assert(PL_get_list(index_name_list, head, index_name_list));
    // read index
    assert(PL_get_list(head, head2, head));
    // assert(PL_get_integer(head2, &name_index_assoc[i].index_bdd));
    assert(PL_get_integer(head2, &opt_data.triple[i].index_bdd));
    // name_index_assoc[i].index_array = i;
    opt_data.triple[i].index_array = i;
    // printf("%d\n",opt_data.triple[i].index_array);

    // read name
    assert(PL_get_list(head, head2, head));
    assert(PL_get_string_chars(head2, &str_tmp, &len_line));
    opt_data.triple[i].name = malloc(len_line + 1); // +1 -> \0
    snprintf(opt_data.triple[i].name,len_line + 1,"%s",str_tmp);
    // printf("%s\n",opt_data.triple[i].name);
	
	// tolgo le (, ) e ,, non so se ti serva
  /*  for(j = 0; j < len_line; j++) {
      if(opt_data.triple[i].name[j] == '(' ||opt_data.triple[i].name[j] == ')' || opt_data.triple[i].name[j] == ',') {
        opt_data.triple[i].name[j] = '_';
      }
    }
  */

    // read prob (float)
    assert(PL_get_list(head, head2, head));
    assert(PL_get_float(head2, &probs_list[i]));
  }

  if (!Cudd_IsConstant(node)) {
    pt_test = retrieve_justs_from_bdd(env,node);
    // print_justs_table(pt_test);
    //symbolic_path = from_paths_to_sym_eq(&pt_test,env,&opt_data,&malloc_size);
    //printf("symbolic_path: %s\n",symbolic_path);
    //assert(PL_put_string_chars(out,symbolic_path));
    if (eol == 1) {
      symbolic_path = from_justs_to_sym_eq(&pt_test,env,&opt_data,&malloc_size);
      printf("symbolic_path: %s\n",symbolic_path);
      assert(PL_put_string_chars(out,symbolic_path)); 
    } else {
      out = generate_prolog_just_list(&pt_test);
    }
  }
  else {
    if (node==Cudd_ReadOne(env->mgr)) {
      assert(PL_put_nil(head));
      assert(PL_put_float(head2,1.0));
      assert(PL_cons_functor(out, minus,head,head2));
      // assert(PL_put_string_chars(out,"1.0"));

    }
    else {
      assert(PL_put_nil(head));
      assert(PL_put_float(head2,0.0));
      assert(PL_cons_functor(out, minus,head,head2));
    }
  }
  
  // forse manca un free(symbolic_path);
  free(probs_list);
  return PL_unify(out,symb_eq_out);
  

}

// END JUSTIFICATION MANAGEMENT
// ======================



install_t install()
/* function required by YAP for intitializing the predicates defined by a C function*/
{
  srand(10);

  PL_register_foreign("init_em",1,init_em,0);
  PL_register_foreign("init_ex",2,init_ex,0);
  PL_register_foreign("end_em",1,end_em,0);
  PL_register_foreign("end_ex",1,end_ex,0);
  PL_register_foreign("add_var",4,add_var,0);
  PL_register_foreign("add_query_var",4,add_query_var,0);
  PL_register_foreign("add_abd_var",4,add_abd_var,0);
  PL_register_foreign("add_opt_var",4,add_opt_var,0);
  PL_register_foreign("equality",4,equality,0);
  PL_register_foreign("and",4,and,0);
  PL_register_foreign("one",2,one,0);
  PL_register_foreign("zero",2,zero,0);
  PL_register_foreign("or",4,or,0);
  PL_register_foreign("bdd_not",3,bdd_not,0);
  PL_register_foreign("create_dot",3,create_dot,0);
  PL_register_foreign("create_dot_string",3,create_dot_string,0);
  PL_register_foreign("init",1,init,0);
  PL_register_foreign("end",1,end,0);
  PL_register_foreign("ret_prob",3,ret_prob,0);
  PL_register_foreign("ret_abd_prob",4,ret_abd_prob,0);
  //PL_register_foreign("ret_opt_prob",10,ret_opt_prob,0);
  PL_register_foreign("ret_map_prob",4,ret_map_prob,0);
  PL_register_foreign("ret_vit_prob",4,ret_vit_prob,0);
  PL_register_foreign("reorder",1,reorder,0);
  PL_register_foreign("make_query_var",3,make_query_var,0);
  PL_register_foreign("em",9,EM,0);
  PL_register_foreign("rand_seed",1,rand_seed,0);
  PL_register_foreign("gamma_sample",3,gamma_sample_pl,0);
  PL_register_foreign("gauss_sample",3,gauss_sample_pl,0);
  PL_register_foreign("uniform_sample",1,uniform_sample_pl,0);
  PL_register_foreign("dirichlet_sample",2,dirichlet_sample_pl,0);
  PL_register_foreign("symmetric_dirichlet_sample",3,symmetric_dirichlet_sample_pl,0);
  PL_register_foreign("discrete_sample",2,discrete_sample_pl,0);
  PL_register_foreign("initial_values",2,initial_values_pl,0);
  PL_register_foreign("add_decision_var",3,add_decision_var,0);
  PL_register_foreign("probability_dd",3,probability_dd,0);
  PL_register_foreign("add_prod",4,add_prod,0);
  PL_register_foreign("add_sum",4,add_sum,0);
  PL_register_foreign("ret_strategy",4,ret_strategy,0);
  PL_register_foreign("compute_best_strategy",5,compute_best_strategy,0);
  PL_register_foreign("debug_cudd_var",2,debug_cudd_var,0);
  // PL_register_foreign("add_const",3,add_const,0);

  PL_register_foreign("ret_influence_prob",4,ret_influence_prob,0);
  // PL_register_foreign("ret_paths_prob",5,ret_paths_prob,0);
  // PL_register_foreign("ret_prob_constr",6,ret_prob_constr,0);
  // PL_register_foreign("test",1,test,0);

//  PL_register_foreign("deref",1,rec_deref,0);
//  PL_register_foreign("garbage_collect",2,garbage_collect,0);
//  PL_register_foreign("bdd_to_add",2,bdd_to_add,0);
//  PL_register_foreign("paths_to_non_zero",2,paths_to_non_zero,0);
//  PL_register_foreign("paths",2,paths,0);
//  PL_register_foreign("dag_size",2,dag_size,0);

// RICCARDO JUSTIFICATION MANAGEMENT
  PL_register_foreign("ret_justs_bdd",5,ret_justs_bdd,0);
}






