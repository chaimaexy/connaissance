from flask import Flask, render_template, request, redirect, url_for, session, jsonify
import re
import itertools
import secrets
import urllib.parse
from enum import Enum
from copy import deepcopy

app = Flask(__name__, template_folder='templates', static_folder='static')
app.secret_key = secrets.token_hex(16)

# --------------------------
# Core data model
# --------------------------

class ConvertTo(Enum):
    ATOMIC = 'atomic'
    NON_CIRCULAR = 'non_circular'

class ConversionFailedError(Exception):
    def __init__(self, message="There was something wrong during conversion"):
        self.message = message
        super().__init__(self.message)

class ConversionNotNeededError(Exception):
    def __init__(self, message="No conversion needed"):
        self.message = message
        super().__init__(self.message)

class Atom:
    def __init__(self, name, is_neg=False):
        self.name = name
        self.is_neg = is_neg

    def flip(self):
        return Atom(self.name, not self.is_neg)

    def display(self):
        return ('¬' + self.name) if self.is_neg else self.name

    def __eq__(self, other):
        return isinstance(other, Atom) and self.name == other.name and self.is_neg == other.is_neg 

    def __hash__(self):
        return hash((self.name, self.is_neg))

    def __repr__(self):
        return self.display()

class RuleObj:
    def __init__(self, name, body, conclusion):
        self.name = name
        self.body = body
        self.conclusion = conclusion

    def display(self):
        if self.body is None:
            return f"{self.name}: {self.conclusion.name} <-"
        else:
            def body_to_str(b):
                if isinstance(b, list):
                    return ', '.join(i.name for i in b)
                elif isinstance(b, Atom):
                    return b.name
                else:
                    return str(b)
            return f"{self.name}: {self.conclusion.name} <- {body_to_str(self.body)}"

    def __repr__(self):
        return self.display()
    
    def to_paths(self):
        """Nouvelle méthode pour générer les chemins comme vos amis"""
        return self._collect_paths(self.conclusion, self.body)

    def _collect_paths(self, current_head, body):
        paths = []
        if body is None:
            paths.append([current_head])
        elif isinstance(body, list):
            for item in body:
                if isinstance(item, RuleObj):
                    nested_paths = item._collect_paths(item.conclusion, item.body)
                    for path in nested_paths:
                        paths.append([current_head] + path)
                else:
                    paths.append([current_head, item])
        elif isinstance(body, Atom):
            paths.append([current_head, body])
        return paths

class Presumption:
    def __init__(self, name, list_atoms, contraries=None):
        self.name = name
        self.list_atoms = list_atoms
        self.contraries = contraries
        if contraries is not None:
            self.dict_contraries = self._build_dict_contraries()
        else:
            self.dict_contraries = None

    def _build_dict_contraries(self):
        d = {}
        for a, c in zip(self.list_atoms, self.contraries):
            d[Atom(a.name, True)] = Atom(c.name, False)
        return d

    def display(self):
        return f"{self.name} = {{ " + ', '.join([l.name for l in self.list_atoms]) + " }}"

    def display_contraries(self):
        if self.contraries is None:
            return None
        pairs = []
        for a, c in zip(self.list_atoms, self.contraries):
            pairs.append(f"{Atom(a.name, True).display()} = {Atom(c.name, False).display()}")
        return "{ " + " , ".join(pairs) + " }"

    def is_contrary(self, x: Atom, y: Atom):
        if self.dict_contraries is None:
            return False
        flip_x = x.flip()
        for key, val in self.dict_contraries.items():
            if key.display() == flip_x.display():
                return val.display() == y.display()
        return False

    def generate_subsets(self):
        combos = []
        for r in range(1, len(self.list_atoms) + 1):
            combos.extend(itertools.combinations(self.list_atoms, r))
        return combos

class ArgumentObj:
    def __init__(self, premises, conclusion):
        self.premises = set(premises)
        self.conclusion = conclusion

    def display(self):
        support_str = ', '.join([lit.display() for lit in self.premises])
        return f"{{ {support_str} }} ⊢ {self.conclusion.display()}"

    def __repr__(self):
        return self.display()

    @staticmethod
    def generate_arguments(rules, presumption: Presumption):
        """Nouvelle version suivant l'approche de vos amis"""
        arguments = []
        
        # Arguments de base (assumptions)
        for ass in presumption.list_atoms:
            arguments.append(ArgumentObj([ass], ass))
        
        # Construction itérative améliorée
        changed = True
        while changed:
            changed = False
            for rule in rules:
                if rule.body is None:
                    # Règle sans précondition
                    new_arg = ArgumentObj([], rule.conclusion)
                    if not any(arg.conclusion == new_arg.conclusion and arg.premises == new_arg.premises for arg in arguments):
                        arguments.append(new_arg)
                        changed = True
                else:
                    # Convertir le corps en liste
                    body_list = rule.body if isinstance(rule.body, list) else [rule.body]
                    
                    # Chercher tous les ensembles d'arguments qui satisfont le corps
                    possible_combinations = [[]]
                    
                    for body_elem in body_list:
                        new_combinations = []
                        # Trouver tous les arguments avec cette conclusion
                        matching_args = [arg for arg in arguments if arg.conclusion == body_elem]
                        
                        for combo in possible_combinations:
                            for arg in matching_args:
                                new_combo = combo + [arg]
                                new_combinations.append(new_combo)
                        
                        possible_combinations = new_combinations
                    
                    # Créer les nouveaux arguments pour chaque combinaison valide
                    for combo in possible_combinations:
                        if len(combo) == len(body_list):  # Tous les éléments du corps sont satisfaits
                            all_premises = set()
                            for arg in combo:
                                all_premises.update(arg.premises)
                            
                            new_arg = ArgumentObj(all_premises, rule.conclusion)
                            
                            # Vérifier si cet argument n'existe pas déjà
                            if not any(arg.conclusion == new_arg.conclusion and arg.premises == new_arg.premises for arg in arguments):
                                arguments.append(new_arg)
                                changed = True
        
        return arguments

class Attack:
    def __init__(self, attacker, attacked):
        self.attacker = attacker
        self.attacked = attacked

    def display(self):
        return f"{self.attacker.display()} attacks {self.attacked.display()}"

    def __repr__(self):
        return self.display()

class NormalAttack(Attack):
    def __init__(self, attacker, attacked):
        super().__init__(attacker, attacked)

    def display(self):
        def part_to_str(p):
            if isinstance(p, (set, tuple, list)):
                return ", ".join(x.display() for x in p)
            elif isinstance(p, ArgumentObj):
                return p.display()
            else:
                return str(p)
        return f"{part_to_str(self.attacker)} attacks {part_to_str(self.attacked)}"

class ReverseAttack(Attack):
    def __init__(self, attacker, attacked):
        super().__init__(attacker, attacked)

    def display(self):
        return NormalAttack.display(self)

class Preferences:
    def __init__(self, more_pref, less_pref):
        self.more_pref = more_pref
        self.less_pref = less_pref

    def display(self):
        more = ', '.join([l.name for l in self.more_pref])
        less = ', '.join([l.name for l in self.less_pref])
        return f"{more} > {less}"

    def __repr__(self):
        return self.display()

class ABAFramework:
    def __init__(self, L, A, R, contraries, preferences=None):
        self.L = L
        self.A = A
        self.R = R
        self.contraries = contraries
        self.preferences = preferences if preferences else []
        self.arguments = None
        self.attacks = None
        self.normal_attacks = None
        self.reverse_attacks = None

    def _is_atomic_rule(self, rule: RuleObj):
        if rule.body is None:
            return False 
        if isinstance(rule.body, Atom):
            return rule.body in self.A.list_atoms
        if isinstance(rule.body, list):
            return all(b in self.A.list_atoms for b in rule.body)
        return False

    def _is_atomic(self):
        values = []
        for rule in self.R:
            values.append(self._is_atomic_rule(rule))
        return all(values)

    def _is_circular(self):
        """Nouvelle vérification de circularité suivant l'approche de vos amis"""
        derived_rules = []
        for rule in self._derive_rules():
            paths = rule.to_paths()
            derived_rules.extend(paths)
        
        # Vérifier la circularité dans les chemins dérivés
        for path in derived_rules:
            # Si un élément apparaît plus d'une fois dans un chemin, il y a circularité
            for element in path:
                if path.count(element) > 1:
                    return True
        
        return False

    def _derive_rules(self):
        """Nouvelle méthode pour dériver les règles comme vos amis"""
        myaba = deepcopy(self)
        changed = False
        for i, rule1 in enumerate(myaba.R):
            if isinstance(rule1.body, list):
                new_body = list(rule1.body)
                for j, value in enumerate(rule1.body):
                    for k, rule2 in enumerate(myaba.R):
                        if i != k and value == rule2.conclusion:
                            new_body[j] = rule2
                            changed = True
                if changed:
                    myaba.R[i] = RuleObj(rule1.name, new_body, rule1.conclusion)
                    return myaba._derive_rules()
            elif isinstance(rule1.body, Atom):
                for j, rule2 in enumerate(myaba.R):
                    if i != j and rule1.body == rule2.conclusion:
                        myaba.R[i] = RuleObj(rule1.name, rule2, rule1.conclusion)
                        return myaba._derive_rules()
        return myaba.R

class LogicEngine:
    def __init__(self, L, R, A: Presumption):
        self.L = L[:]
        self.R = R[:]
        self.A = A

    def is_atomic_rule(self, rule: RuleObj):
        """Vérifie si une règle est atomique (tous les éléments du corps sont des assumptions)"""
        if rule.body is None:
            return True  # Règle sans corps est considérée comme atomique
        
        if isinstance(rule.body, Atom):
            return rule.body in self.A.list_atoms
        
        if isinstance(rule.body, list):
            return all(b in self.A.list_atoms for b in rule.body)
        
        return False

    def circular_to_noncircular(self):
        """Nouvelle version suivant EXACTEMENT l'approche de vos amis"""
        A_set = set(self.A.list_atoms)
        
        # Identifier les littéraux non-assumptions
        L_non_a = [l for l in self.L if l not in A_set]
        
        if not L_non_a:
            return ["Le système ABA est déjà non-circulaire.", "Aucune conversion nécessaire."], []
        
        # k = |L\A| (nombre de littéraux non-assumptions)
        k = len(L_non_a)
        new_rules = []
        to_add_literals = set()
        
        for rule in self.R:
            # Si la règle est atomique (tous les éléments du corps sont des assumptions)
            if self.is_atomic_rule(rule):
                # Générer de nouvelles règles avec indices pour les règles atomiques
                for i in range(1, k + 1):
                    if i != k:
                        # Créer une nouvelle règle avec head indexé
                        new_head = Atom(f"{rule.conclusion.name}_{i}", rule.conclusion.is_neg)
                        to_add_literals.add(new_head)
                        new_rule = RuleObj(f"{rule.name}_{i}", rule.body, new_head)
                        new_rules.append(new_rule)
                    else:
                        # Dernière règle avec le head original
                        new_rules.append(rule)
            else:
                # Si la règle n'est pas atomique, traiter le corps
                body_list = rule.body if isinstance(rule.body, list) else [rule.body]
                
                # Générer pour i de 2 à k
                for i in range(2, k + 1):
                    new_body = []
                    
                    # Traiter chaque élément du corps
                    for elem in body_list:
                        if elem in A_set:
                            # Garder les assumptions telles quelles
                            new_body.append(elem)
                        else:
                            # Indexer les littéraux non-assumptions dans le corps
                            new_elem = Atom(f"{elem.name}_{i-1}", elem.is_neg)
                            to_add_literals.add(new_elem)
                            new_body.append(new_elem)
                    
                    # Préparer le body final
                    body_final = new_body if len(new_body) > 1 else (new_body[0] if new_body else None)
                    
                    if i != k:
                        # Créer une nouvelle règle avec head indexé
                        new_head = Atom(f"{rule.conclusion.name}_{i}", rule.conclusion.is_neg)
                        to_add_literals.add(new_head)
                        new_rule = RuleObj(f"{rule.name}_{i}", body_final, new_head)
                        new_rules.append(new_rule)
                    else:
                        # Dernière règle avec le head original
                        new_rule = RuleObj(rule.name, body_final, rule.conclusion)
                        new_rules.append(new_rule)
        
        # Mettre à jour le langage avec les nouveaux littéraux
        for lit in to_add_literals:
            if lit not in self.L:
                self.L.append(lit)
        
        # Préparer l'affichage des résultats
        rules_display = [r.display() for r in new_rules]
        lits_display = [l.display() for l in self.L]
        
        return rules_display, lits_display

    def to_atomic(self):
        """Nouvelle version suivant l'approche de vos amis"""
        # Build list of non-assumption literals
        L_non_a = [l for l in self.L if l not in self.A.list_atoms]

        # Créer les nouvelles assumptions
        for s in L_non_a:
            s_d = Atom(f"{s.name}_d", s.is_neg)
            s_nd = Atom(f"{s.name}_nd", s.is_neg)
            
            # Ajouter aux assumptions et langage
            if s_d not in self.A.list_atoms:
                self.A.list_atoms.append(s_d)
            if s_nd not in self.A.list_atoms:
                self.A.list_atoms.append(s_nd)
            if s_d not in self.L:
                self.L.append(s_d)
            if s_nd not in self.L:
                self.L.append(s_nd)

        # Mettre à jour les règles
        new_rules = []
        for rule in self.R:
            if rule.body is None:
                new_rules.append(rule)
            else:
                new_body = []
                body_list = rule.body if isinstance(rule.body, list) else [rule.body]
                
                for k in body_list:
                    if k in self.A.list_atoms:
                        new_body.append(k)
                    else:
                        new_body.append(Atom(f"{k.name}_d", False))
                
                body_final = new_body if len(new_body) > 1 else (new_body[0] if new_body else None)
                new_rule = RuleObj(rule.name, body_final, rule.conclusion)
                new_rules.append(new_rule)

        self.R = new_rules

        # Préparer les résultats
        list_A = [l.display() for l in self.A.list_atoms]
        list_L = [l.display() for l in self.L]
        
        # Générer les contraries
        cont_pairs = []
        for s in L_non_a:
            cont_pairs.append(f"C({s.name}_d): {s.name}_nd")
            cont_pairs.append(f"C({s.name}_nd): {s.name}")
        
        rules_list = [r.display() for r in self.R]
        
        return {
            'assumptions_literals': [list_A, list_L],
            'contraries': cont_pairs,
            'rules': rules_list
        }

class AcceptabilityEngine:
    def __init__(self, arguments, attacks):
        self.arguments = arguments
        self.attack_graph = self._build_attack_graph(attacks)
        self.arg_set = set(arguments)

    def _build_attack_graph(self, attacks):
        graph = {arg: set() for arg in self.arguments}
        for attack in attacks:
            if isinstance(attack.attacker, ArgumentObj) and isinstance(attack.attacked, ArgumentObj):
                if attack.attacker in graph and attack.attacked in self.arguments:
                     graph[attack.attacker].add(attack.attacked)
        return graph

    def is_conflict_free(self, subset):
        for arg1 in subset:
            for arg2 in subset:
                if arg2 in self.attack_graph.get(arg1, set()):
                    return False
        return True

    def defends(self, subset, arg_to_defend):
        attackers = {a for a, targets in self.attack_graph.items() 
                     if arg_to_defend in targets and a not in subset}
                     
        for attacker in attackers:
            is_defended = False
            for defender in subset:
                if attacker in self.attack_graph.get(defender, set()):
                    is_defended = True
                    break
            if not is_defended:
                 return False
        return True

    def get_admissible_sets(self):
        Ga = self.arguments
        admissible = []
        
        all_subsets = []
        for i in range(len(Ga) + 1):
            all_subsets.extend(itertools.combinations(Ga, i))
            
        for subset_tuple in all_subsets:
            subset = set(subset_tuple)
            
            if not self.is_conflict_free(subset):
                continue
            
            is_admissible = True
            for arg in subset:
                if not self.defends(subset, arg):
                    is_admissible = False
                    break
            
            if is_admissible:
                formatted_set = tuple(sorted([a.display() for a in subset]))
                formatted_admissible = [tuple(sorted([a.display() for a in adm])) for adm in admissible]
                
                if formatted_set not in formatted_admissible:
                    admissible.append(subset)

        formatted_result = []
        for i, adm_set in enumerate(admissible):
            display_args = ", ".join([a.display() for a in adm_set])
            formatted_result.append(f"Admissible Set S{i+1}: {{ {display_args} }}")
            
        return formatted_result

# Helper functions
def generate_attacks(arguments, presumption: Presumption):
    attacks = []
    if presumption.contraries is None:
        return attacks

    for arg1 in arguments:
        for arg2 in arguments:
            if arg1 == arg2:  # Éviter les auto-attaques
                continue
                
            # Vérifier si la conclusion de arg1 est le contraire d'une prémisse de arg2
            for premise in arg2.premises:
                if presumption.is_contrary(premise, arg1.conclusion):
                    attacks.append(Attack(arg1, arg2))
                    break
    return attacks

def generate_cyto_data(Ga, attacks):
    cyto_nodes = []
    ga_map_index = {}
    
    for i, arg in enumerate(Ga):
        node_id = f'A{i}'
        label = f'A{i}: {arg.conclusion.display()}'
        cyto_nodes.append({
            'data': {
                'id': node_id, 
                'label': label
            }
        })
        ga_map_index[arg] = node_id
    
    cyto_edges = []
    edge_counter = 0
    
    for attack in attacks:
        try:
            if (isinstance(attack.attacker, ArgumentObj) and 
                isinstance(attack.attacked, ArgumentObj)):
                
                attacker_id = ga_map_index.get(attack.attacker)
                attacked_id = ga_map_index.get(attack.attacked)
                
                if attacker_id and attacked_id:
                    edge_id = f'e{edge_counter}'
                    cyto_edges.append({
                        'data': {
                            'id': edge_id,
                            'source': attacker_id, 
                            'target': attacked_id
                        }
                    })
                    edge_counter += 1
                    
        except Exception:
            continue

    return cyto_nodes + cyto_edges

def generate_normal_reverse_attacks(presumption: Presumption, prefs: Preferences, rules: list):
    subsets = presumption.generate_subsets()
    arguments = ArgumentObj.generate_arguments(rules, presumption)
    normal_attacks = []
    reverse_attacks = []

    for sub1 in subsets:
        for sub2 in subsets:
            for arg in arguments:
                leaves = arg.premises
                conclusion = arg.conclusion
                if all(leaf in sub1 for leaf in leaves):
                    for y in sub2:
                        if presumption.is_contrary(y, conclusion):
                            if all(not (p in prefs.less_pref and y in prefs.more_pref) for p in leaves):
                                na = NormalAttack(sub1, sub2)
                                if na.display() not in [n.display() for n in normal_attacks]:
                                    normal_attacks.append(na)

                if all(leaf in sub2 for leaf in leaves):
                    for x in sub1:
                        if presumption.is_contrary(x, conclusion):
                            for p_ in leaves:
                                if p_ in prefs.less_pref and x in prefs.more_pref:
                                    ra = ReverseAttack(sub1, sub2)
                                    if ra.display() not in [r.display() for r in reverse_attacks]:
                                        reverse_attacks.append(ra)
    return normal_attacks, reverse_attacks

def parse_input(text):
    L, A, C, R, PREF = [], [], {}, {}, ""
    lines = text.strip().splitlines()
    for line in lines:
        line = line.strip()
        if not line:
            continue
        if line.startswith("L:"):
            content = re.search(r'\[(.*?)\]', line)
            if content:
                L = [x.strip() for x in content.group(1).split(',') if x.strip()]
        elif line.startswith("A:"):
            content = re.search(r'\[(.*?)\]', line)
            if content:
                A = [x.strip() for x in content.group(1).split(',') if x.strip()]
        elif line.startswith("C("):
            match = re.match(r'C\((\w+)\):\s*(\w+)', line)
            if match:
                key, value = match.groups()
                C[key] = value
        elif re.match(r'\[r\d+\]:', line):
            match = re.match(r'\[(r\d+)\]:\s*(.+)', line)
            if match:
                key, value = match.groups()
                R[key] = value
        elif line.startswith("PREF:"):
            match = re.search(r'PREF:\s*(.+)', line)
            if match:
                PREF = match.group(1).strip()
    return L, A, C, R, PREF

def handle_preferences_assumptions(L, A, C, R, PREF):
    result = []
    
    if PREF:
        result.append(f"Préférences: {PREF}")
    else:
        result.append("Aucune préférence définie")
    
    result.append(f"Assumptions (A): {[a.display() for a in A.list_atoms]}")
    
    if A.contraries:
        result.append(f"Contraires: {A.display_contraries()}")
    else:
        result.append("Aucun contraire défini")
    
    return result

def handle_normal_reverse_attacks(L, A, C, R, PREF):
    more_pref = []
    less_pref = []
    if PREF and '>' in PREF:
        parts = PREF.split('>')
        if len(parts) == 2:
            more_pref = [Atom(p.strip()) for p in parts[0].split(',') if p.strip()]
            less_pref = [Atom(p.strip()) for p in parts[1].split(',') if p.strip()]
    
    prefs = Preferences(more_pref, less_pref)
    
    normal_attacks, reverse_attacks = generate_normal_reverse_attacks(A, prefs, R)
    
    normal_display = [f"Attaque normale {i+1}: {att.display()}" for i, att in enumerate(normal_attacks)]
    reverse_display = [f"Attaque inverse {i+1}: {att.display()}" for i, att in enumerate(reverse_attacks)]
    
    return [normal_display, reverse_display]

# Flask routes 
@app.route('/', methods=['GET', 'POST'])
def index():
    error = None
    user_input = ""
    
    if request.method == 'POST':
        input_text = request.form.get('text_input', '')
        user_input = input_text

        Ltxt, Atxt, Ctxt, Rtxt, PREF = parse_input(input_text)
        if not Ltxt or not Atxt:
            error = "Entrée invalide : format attendu (ex: L: [a,b,c] et A: [a,b])."
            return render_template('index.html', error=error, project_name="Part1 Logic System", user_input=user_input)
            
        return redirect(url_for('options', user_input=urllib.parse.quote(input_text)))
    
    return render_template('index.html', project_name="Part1 Logic System", user_input=user_input)

@app.route('/options/<path:user_input>', methods=['GET', 'POST'])
def options(user_input):
    decoded_input = urllib.parse.unquote(user_input)
    user_input_path = user_input 
    
    Ltexte, Atexte, Ctexte, Rdict, PREF = parse_input(decoded_input)
    L = [Atom(item) for item in Ltexte]
    
    keys = list(Ctexte.keys())
    values = list(Ctexte.values())
    pres_atoms = []
    pres_contraries = []
    for k, v in zip(keys, values):
        if k in Atexte:
            pres_atoms.append(Atom(k))
            pres_contraries.append(Atom(v))
    A = Presumption('A', pres_atoms, pres_contraries if pres_contraries else None)

    list_conclusions, list_premises, rule_names = [], [], []
    for key, value in Rdict.items():
        if '<-' in value:
            parts = value.split('<-')
            concl = parts[0].strip()
            prem = parts[1].strip()
        else:
            concl = value.strip()
            prem = ''
        list_conclusions.append(concl)
        list_premises.append(prem)
        rule_names.append(key)

    conclusions_atoms = [Atom(c) for c in list_conclusions]
    premises_parsed = []
    for item in list_premises:
        if item == '' or len(item) == 0:
            premises_parsed.append(None)
        elif len(item) == 1 and item.isalpha():
            premises_parsed.append(Atom(item))
        else:
            parts = [p.strip() for p in re.split(r',\s*', item) if p.strip()]
            premises_parsed.append([Atom(p) for p in parts] if parts else None)

    R = [RuleObj(name, body, concl) for name, body, concl in zip(rule_names, premises_parsed, conclusions_atoms)]

    if request.method == 'POST':
        action = request.form.get('action')
        
        session.clear()
        
        if action == 'create_arguments':
            Ga = ArgumentObj.generate_arguments(R, A) 
            result = [f"Argument {i+1}: {arg.display()}" for i, arg in enumerate(Ga)]
            session['result'] = result
            session['show_graph'] = False
            
        elif action == 'create_attacks':
            Ga = ArgumentObj.generate_arguments(R, A) 
            attacks = generate_attacks(Ga, A)
            result = [f"Attaque {i+1}: {att.display()}" for i, att in enumerate(attacks)]
            session['result'] = result
            
            if Ga and attacks:
                cyto_elements = generate_cyto_data(Ga, attacks)
                session['cyto_elements'] = cyto_elements
                session['show_graph'] = True
            else:
                session['show_graph'] = False
                
        elif action == 'calculate_admissible':
            Ga = ArgumentObj.generate_arguments(R, A) 
            attacks = generate_attacks(Ga, A)
            engine = AcceptabilityEngine(Ga, attacks)
            result = engine.get_admissible_sets()
            session['result'] = result
            
            if Ga and attacks:
                cyto_elements = generate_cyto_data(Ga, attacks)
                session['cyto_elements'] = cyto_elements
                session['show_graph'] = True
            else:
                session['show_graph'] = False
                
        elif action == 'auto_convert_non_circular':
            engine = LogicEngine(L, R, A)
            rules_display, lits_display = engine.circular_to_noncircular()
            result = []
            result.append("=== CONVERSION NON-CIRCULAIRE ===")
            result.append("Nouvelles règles:")
            result.extend(rules_display)
            result.append("Nouveaux littéraux:")
            result.extend(lits_display)
            session['result'] = result
            session['show_graph'] = False
            
        elif action == 'auto_convert_atomic':
            engine = LogicEngine(L, R, A)
            atomic_result = engine.to_atomic()
            # Handle the dictionary result properly
            if isinstance(atomic_result, dict):
                result = []
                result.append("=== CONVERSION ATOMIQUE ===")
                result.append("Nouvelles Assumptions (A) et Littéraux (L)")
                result.append(f"A: {atomic_result['assumptions_literals'][0]}")
                result.append(f"L: {atomic_result['assumptions_literals'][1]}")
                result.append("Nouveaux Contraires (C)")
                result.extend(atomic_result['contraries'])
                result.append("Nouvelles Règles (R)")
                result.extend(atomic_result['rules'])
            else:
                result = atomic_result
            session['result'] = result
            session['show_graph'] = False

        elif action == 'handle_preferences_assumptions':
            result = handle_preferences_assumptions(L, A, Ctexte, R, PREF)
            session['result'] = result
            session['show_graph'] = False

        elif action == 'handle_normal_reverse_attacks':
            result = handle_normal_reverse_attacks(L, A, Ctexte, R, PREF)
            session['result'] = result
            session['show_graph'] = False

        return redirect(url_for('result', user_input_path=user_input_path))
    
    return render_template('index.html', 
                           from_options=True, 
                           project_name="Part1 Logic System", 
                           user_input_path=user_input_path,
                           user_input=decoded_input)

@app.route('/result/<path:user_input_path>')
def result(user_input_path):
    result = session.get('result', [])
    decoded_input = urllib.parse.unquote(user_input_path)
    
    cyto_elements = session.get('cyto_elements', [])
    show_graph = session.get('show_graph', False)
    
    return render_template('index.html', 
                           result=result, 
                           project_name="Part1 Logic System",
                           from_options=True, 
                           user_input_path=user_input_path,
                           user_input=decoded_input,
                           cyto_elements=cyto_elements, 
                           show_graph=show_graph)

@app.route('/api/graph_data')
def api_graph_data():
    cyto_elements = session.get('cyto_elements', [])
    return jsonify(cyto_elements)

if __name__ == '__main__':
    app.run(debug=True)