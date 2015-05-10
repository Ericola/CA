#include <Basic_block.h>


//static
void Basic_block::show_dependances(Instruction *i1, Instruction *i2){
   
  if(i1->is_dep_RAW1(i2)) 
    cout<<"Dependance i"<<i1->get_index()<<"->i"<<i2->get_index()<<": RAW1"<<endl; 
  if(i1->is_dep_RAW2(i2)) 
    cout<<"Dependance i"<<i1->get_index()<<"->i"<<i2->get_index()<<": RAW2"<<endl;
   
  if(i1->is_dep_WAR(i2)) 
    cout<<"Dependance i"<<i1->get_index()<<"->i"<<i2->get_index()<<": WAR"<<endl;
   
  if(i1->is_dep_WAW(i2)) 
    cout<<"Dependance i"<<i1->get_index()<<"->i"<<i2->get_index()<<": WAW"<<endl;
   
  if(i1->is_dep_MEM(i2)) 
    cout<<"Dependance i"<<i1->get_index()<<"->i"<<i2->get_index()<<": MEM"<<endl;
   
}

Basic_block::Basic_block(){
  _head = NULL;
  _end = NULL;
  _branch = NULL;
  _index = 0;
  _nb_instr = 0;
  _firstInst=NULL;
  _lastInst=NULL;
  dep_done = false;
  use_def_done = false;
   
  for(int i=0; i<NB_REG; i++){
    Use[i]= false;
    LiveIn[i] = false;
    LiveOut[i] = false;
    Def[i] = false;
    DefLiveOut[i] = -1;
  }

  for(int i=0; i<NB_MAX_BB; i++){
    Domin[i]= true;
  }

}


Basic_block::~Basic_block(){}


void Basic_block::set_index(int i){
  _index = i;
}

int Basic_block::get_index(){
  return _index;
}

void Basic_block::set_head(Line *head){
  _head = head;
}

void Basic_block::set_end(Line *end){
  _end = end;
}

Line* Basic_block::get_head(){
  return _head;
}

Line* Basic_block::get_end(){
  return _end;
}

void Basic_block::set_successor1(Basic_block *BB){
  _succ.push_front(BB);
}

Basic_block *Basic_block::get_successor1(){
  if (_succ.size()>0)
    return _succ.front();
  else 
    return NULL;
}

void Basic_block::set_successor2(Basic_block *BB){	
  _succ.push_back(BB);
}

Basic_block *Basic_block::get_successor2(){
  if (_succ.size()> 1)
    return _succ.back();
  else 
    return NULL;
}

void Basic_block::set_predecessor(Basic_block *BB){
  _pred.push_back(BB);
}

Basic_block *Basic_block::get_predecessor(int index){

  list<Basic_block*>::iterator it;
  it=_pred.begin();
  int size=(int)_pred.size();
  if(index< size){
    for (int i=0; i<index; i++, it++);
    return *it;	
  }
  else cout<<"Error: index is bigger than the size of the list"<<endl; 	
  return _pred.back();
	
}

int Basic_block::get_nb_succ(){
  return _succ.size();
}

int Basic_block::get_nb_pred(){
  return _pred.size();
}

void Basic_block::set_branch(Line* br){
  _branch=br;
}

Line* Basic_block::get_branch(){
  return _branch;
}

void Basic_block::display(){
  cout<<"Begin BB"<<endl;
  Line* element = _head;
  int i=0;
  if(element == _end)	
    cout << _head->get_content() <<endl;
  
  while(element != _end->get_next()){
    if(element->isInst()){
      cout<<"i"<<i<<" ";
      i++;
    }
    if(!element->isDirective())
      cout <<element->get_content() <<endl;
      
    element = element->get_next();
  }
  cout<<"End BB"<<endl;
}

int Basic_block::size(){
  Line* element = _head;
  int lenght=0;
  while(element != _end){
    lenght++;
    if(element->get_next()==_end)	
      break;
    else 
      element = element->get_next();
  }
  return lenght;
}	


void Basic_block::restitution(string const filename){	
  Line* element = _head;
  ofstream monflux(filename.c_str(), ios::app);
  if(monflux){
    monflux<<"Begin BB"<<endl;
    if(element == _end)	
      monflux << _head->get_content() <<endl;
    while(element != _end)
      {
	if(element->isInst()) 
	  monflux<<"\t";
	if(!element->isDirective())
	  monflux << element->get_content()<<endl ;
		
	if(element->get_next()==_end){
	  if(element->get_next()->isInst()) 
	    monflux<<"\t";
	  if(!element->isDirective())
	    monflux << element->get_next()->get_content()<<endl;
	  break;
	}
	else element = element->get_next();
      }
    monflux<<"End BB\n\n"<<endl;		
  }
  else {
    cout<<"Error cannot open the file"<<endl;
  }
  monflux.close();

}

bool Basic_block::is_labeled(){
  if (_head->isLabel()){
    return true;
  }
  else return false;
}

int Basic_block::get_nb_inst(){   
  if (_nb_instr == 0)
    link_instructions();
  return _nb_instr;
    
}

Instruction* Basic_block::get_instruction_at_index(int index){
  Instruction *inst;
   
  if(index >= get_nb_inst()){
    return NULL;
  }
   
  inst=get_first_instruction();

  for(int i=0; i<index; i++, inst=inst->get_next());

  return inst;
}

Line* Basic_block::get_first_line_instruction(){
   
  Line *current = _head;
  while(!current->isInst()){
    current=current->get_next();
    if(current==_end)
      return NULL;
  }
  return current;
}

Instruction* Basic_block::get_first_instruction(){
  if(_firstInst==NULL){
    _firstInst= getInst(this->get_first_line_instruction());
    this->link_instructions();
  }
  return _firstInst;
}

Instruction* Basic_block::get_last_instruction(){
  if(_lastInst==NULL)
    this->link_instructions();
  return _lastInst;
}


/* link_instructions  numérote les instructions du bloc */
/* remplit le champ nb d'instructions du bloc (_nb_instr) */
/* remplit le champ derniere instruction du bloc (_lastInst) */
void Basic_block::link_instructions(){

  int index=0;
  Line *current, *next;
  current=get_first_line_instruction();
  next=current->get_next();

  Instruction *i1 = getInst(current);

  i1->set_index(index);
  index++;
  Instruction *i2;
   
  //Calcul des successeurs
  while(current != _end){
   
    while(!next->isInst()){
      next=next->get_next();
      if(next==_end){
	if(next->isInst())
	  break;
	else{
	  _lastInst = i1;
	  _nb_instr = index;
	  return;
	}
      }
    }
      
    i2 = getInst(next);
    i2->set_index(index);
    index++;
    i1->set_link_succ_pred(i2);
      
    i1=i2;
    current=next;
    next=next->get_next();
  }
  _lastInst = i1;
  _nb_instr = index;
}

bool Basic_block::is_delayed_slot(Instruction *i){
  if (get_branch()== NULL)
    return false;
  int j = (getInst(get_branch()))->get_index();
  return (j < i-> get_index());

}

/* set_link_succ_pred : ajoute succ comme successeur de this et ajoute this comme prédécesseur de succ
 */

void Basic_block::set_link_succ_pred(Basic_block* succ){
  _succ.push_back(succ);
  succ->set_predecessor(this);
}

/* add_dep_link ajoute la dépendance avec pred à la liste des dependances précédesseurs de succ */
/* ajoute la dependance avec succ à la liste des dépendances successeurs de pred */

/* dep est une structure de données contenant une instruction et  un type de dépendance */

void add_dep_link(Instruction *pred, Instruction* succ, t_Dep type){
  dep *d;
  d=(dep*)malloc(sizeof(dep));
  d->inst=succ;
  d->type=type;
  pred->add_succ_dep(d);
   
  d=(dep*)malloc(sizeof(dep));
  d->inst=pred;
  d->type=type;
  succ->add_pred_dep(d);
}


/* calcul des dépendances entre les instructions dans le bloc  */
/* une instruction a au plus 1 reg dest et 2 reg sources */
/* Attention le reg source peut être 2 fois le même */ 
/* Utiliser les méthodes is_dep_RAW1, is_dep_RAW2, is_dep_WAR, is_dep_WAW, is_dep_MEM pour déterminer les dépendances */

/* ne pas oublier les dépendances de controle avec le branchement s'il y en a un */

/* utiliser la fonction add_dep_link ci-dessus qui ajoute à la liste des dépendances pred et succ une dependance entre 2 instructions */

void Basic_block::comput_pred_succ_dep(){
   
  // IMPORTANT : laisser les 2 instructions ci-dessous 
  link_instructions();
  if (dep_done) return;
  int i, j;
  Instruction *inst;
  for(i = this->get_nb_inst() -1 ; i>= 0; i--){
    inst = this->get_instruction_at_index(i);
    for(j = this->get_nb_inst() - 1; j>= 0; j--){
      if(i == j)
	continue;
      Instruction *inst2 = this->get_instruction_at_index(j);
      t_Dep t = inst->is_dependant(inst2);

      if(inst->is_dep_RAW(inst2)){
      	add_dep_link(inst, inst2, RAW);
      	break;
      }		  
     
      if(inst->is_dep_WAR(inst2)){
      	add_dep_link(inst, inst2,WAR);
      }
      if(inst->is_dep_WAW(inst2)){
      	add_dep_link(inst, inst2, WAW);
      }

      if(inst->is_dep_MEM(inst2)){
      	add_dep_link(inst, inst2, t);
      }
    }
  }

  for(i = 0; i < this->get_nb_inst(); i++){
    inst = this->get_instruction_at_index(i);
    if(inst->get_nb_succ() == 0 && !(inst->is_branch()) && !(inst->is_nop()) && !(this->is_delayed_slot(inst))){
      add_dep_link(inst, (Instruction*)(this->get_branch()), CONTROL);
    }
  }

  // NE PAS ENLEVER : cette fonction ne doit être appelée qu'une seule fois
  dep_done = true;
  return;
}



void Basic_block::reset_pred_succ_dep(){

  Instruction *ic=get_first_instruction();
  while (ic){
    ic -> reset_pred_succ_dep();
    ic = ic -> get_next();
  }
  dep_done = false;
  return;
}


/* calcul le nb de cycles pour executer le BB, on suppose qu'une instruction peut sortir du pipeline à chaque cycle, il faut trouver les cycles de gel induit par les dépendances */

int Basic_block::nb_cycles(){
  
  int nb = 0;
  int depRaw = 0;
  int i = 0;
  int j = 0;
  int k = 0;
  Instruction *ic;
  for(i = 0; i < this->get_nb_inst(); i++){
    dep* d;
    depRaw = 0;
    ic = this->get_instruction_at_index(i);
    for(j = 0; j < ic->get_nb_pred(); j++){
      d = ic->get_pred_dep(j);
      if(d->type == RAW){
	depRaw = 1;
	k = j;
	break;
      }
    }
    if(depRaw == 1){
      nb = nb + 1 + delai(ic->get_type(), this->get_instruction_at_index(k)->get_type());
    }
    else{
      nb++;
    }
  }
  return nb;
}

/* 
   calcule DEF et USE pour l'analyse de registre vivant 
   à la fin on doit avoir
   USE[i] vaut 1 si $i est utilisé dans le bloc avant d'être potentiellement défini dans le bloc
   DEF[i] vaut 1 si $i est défini dans le bloc 
******************/

void Basic_block::compute_use_def(void){

  int i;
  Instruction *ic;
  cout <<"debut compute_use_def"<< endl;
  for(i=0;i<get_nb_inst();i++) {
    ic = this->get_instruction_at_index(i);
    if(ic != NULL) {
      if(ic->get_reg_dst() != NULL) {
	Def[ic->get_reg_dst()->get_reg()] = true;
      }
      if(ic->get_reg_src1() != NULL) {
	Use[ic->get_reg_src1()->get_reg()] = true;
      }
      if(ic->get_reg_src2() != NULL) {
	Use[ic->get_reg_src2()->get_reg()] = true;
      }
    }
  }
  cout <<"fin compute_use_def"<< endl;
  return;
}

/**** compute_def_liveout 
      à la fin de la fonction on doit avoir
      DefLiveOut[i] vaut l'index de l'instruction du bloc qui définit $i si $i vivant en sortie seulement
      Si $i est défini plusieurs fois c'est l'instruction avec l'index le plus grand
*****/
void Basic_block::compute_def_liveout(){
  for(int i=0;i<get_nb_inst();i++) {
    Instruction*  ic = this->get_instruction_at_index(i);
    if(ic != NULL) {
      if(ic->get_reg_dst() != NULL) {
	if(LiveOut[ic->get_reg_dst()->get_reg()]) {
	  DefLiveOut[ic->get_reg_dst()->get_reg()] = i;
	}
      }
    }
  }
}



/**** renomme les registres renommables en utilisant comme registres disponibles ceux dont le numéro est dans la liste paramètre 
*****/
void Basic_block::reg_rename(list<int> *frees){
  list<int>::iterator it = frees->begin();
  Instruction* ic;
  int reg;
  cout<<"debut reg_rename"<<endl;
  for(int i = 0;i<get_nb_inst();i++) {
    ic = this->get_instruction_at_index(i);
    if(ic != NULL) {
      if(ic->get_reg_dst() != NULL) {
	if(DefLiveOut[ic->get_reg_dst()->get_reg()] == -1 && ic->get_reg_dst()->get_reg() != 0){
	  if(*it == 0){
	    it++;
	  }
	  reg = *it;
	  it++;
	  int tmpreg = ic->get_reg_dst()->get_reg();
	  ic->get_reg_dst()->set_reg(reg);
	  it++;
	   for(int j=0;j<get_nb_inst();j++) {
	     Instruction*  ic = this->get_instruction_at_index(j);
	     if(ic->get_reg_src1()!= NULL){
	       if(ic->get_reg_src1()->get_reg() == tmpreg){
	
		 ic->get_reg_src1()->set_reg(reg);
	       }
	     }
	     if(ic->get_reg_src2()!= NULL){
	       if(ic->get_reg_src2()->get_reg() == tmpreg){
		
		 ic->get_reg_src2()->set_reg(reg);
	       }
	     }
	   }
	}
      }
    }
  }	
  cout<<"fin reg_rename"<<endl;
  return;
}


/**** renomme les registres renommables en utilisant comme registres disponibles ceux disponible pour le bloc d'après l'analyse de vivacité et def-use

*****/
void Basic_block::reg_rename(){
  cout <<"reg_rename(void)"<< endl;
  // Calcul de defInst et defLiveOut
  this->compute_use_def();
  this->compute_def_liveout();
  // defInst(bb)
  list<int> defInst; 
  //defLiveout(bb)
  list<int> defLiveout;
  //R
  list<int> R;
  R.clear();
  //Calcul de defInst
  for(int i = 0; i < get_nb_inst(); i++){
    Instruction*  ic = this->get_instruction_at_index(i);
    if(ic != NULL) {
      if(ic->get_reg_dst() != NULL) {
	if(Def[ic->get_reg_dst()->get_reg()]) {
	  list<int>::iterator contains = find(defInst.begin(), defInst.end(), ic->get_reg_dst()->get_reg());
	  if(contains != defInst.end()){ // on evite les doublons
	    defInst.push_back(ic->get_reg_dst()->get_reg());			
	  }
	}
      }
    }
  }

  //calcul de defLiveOut
  for(int i = 0; i < get_nb_inst(); i++){
    Instruction*  ic = this->get_instruction_at_index(i);
    if(ic != NULL) {
      if(ic->get_reg_dst() != NULL) {
	if(DefLiveOut[ic->get_reg_dst()->get_reg()]) {
	  list<int>::iterator contains = find(defInst.begin(), defInst.end(), ic->get_reg_dst()->get_reg());
	  list<int>::iterator containsDefLiveOut = find(defLiveout.begin(), defLiveout.end(), ic->get_reg_dst()->get_reg());
	  if(contains != defInst.end() && containsDefLiveOut != defLiveout.end()){ // on evite lesdoublons
	    defLiveout.push_back(ic->get_reg_dst()->get_reg());			
	  }
	}
      }
    }
  }

  //calcul de R
  int v = 0;
  while(!defInst.empty()){
    v = defInst.front();
    defInst.pop_front();
    list<int>::iterator containsDefLiveOut = find(defLiveout.begin(), defLiveout.end(), v);
    if(containsDefLiveOut != defLiveout.end()){
      R.push_back(v);
    }
  }
  R.remove(0);
  reg_rename(&R);
  
  cout <<"fin reg_rename(void)"<< endl;
}


void Basic_block::apply_scheduling(list <Node_dfg*> *new_order){
  list <Node_dfg*>::iterator it=new_order->begin();
  Instruction *inst=(*it)->get_instruction();
  Line *n=_head, *prevn=NULL;
  Line *end_next = _end->get_next();
  if(!n){
    cout<<"wrong bb : cannot apply"<<endl;
    return;
  }
   
  while(!n->isInst()){
    prevn=n;
    n=n->get_next();
    if(n==_end){
      cout<<"wrong bb : cannot apply"<<endl;
      return;
    }
  }
   
  //y'a des instructions, on sait pas si c'est le bon BB, mais on va supposer que oui
  inst->set_index(0);
  inst->set_prev(NULL);
  _firstInst = inst;
  n = inst;
   
  if(prevn){
    prevn->set_next(n);
    n->set_prev(prevn);
  }
  else{
    set_head(n);
  }

  int i;
  it++;
  for(i=1; it!=new_order->end(); it++, i++){

    inst->set_link_succ_pred((*it)->get_instruction());
     
    inst=(*it)->get_instruction();
    inst->set_index(i);
    prevn = n;
    n = inst;
    prevn->set_next(n);
    n->set_prev(prevn);
  }
  inst->set_next(NULL);
  _lastInst = inst;
  set_end(n);
  n->set_next(end_next);
  return;
}

/* permet de tester des choses sur un bloc de base, par exemple la construction d'un DFG, à venir ... là ne fait rien qu'afficher le BB */
void Basic_block::test(){
  cout << "test du BB " << get_index() << endl;
  display();
  cout << "nb de successeur : " << get_nb_succ() << endl;
  int nbsucc = get_nb_succ() ;
  if (nbsucc >= 1 && get_successor1())
    cout << "succ1 : " << get_successor1()-> get_index();
  if (nbsucc >= 2 && get_successor2())
    cout << " succ2 : " << get_successor2()-> get_index();
  cout << endl << "nb de predecesseurs : " << get_nb_pred() << endl ;
  
  int size=(int)_pred.size();
  for (int i = 0; i < size; i++){
    if (get_predecessor(i) != NULL)
      cout << "pred "<< i <<  " : " << get_predecessor(i)-> get_index() << "; ";
  }
  cout << endl;
}
