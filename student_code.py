import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """

        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################
        # Student code goes here
        if isinstance(fact_or_rule, Rule):
            if fact_or_rule not in self.rules:
                return
            rule_fact = self._get_rule(fact_or_rule)
            if not rule_fact:
                return
        elif isinstance(fact_or_rule, Fact):
            if fact_or_rule not in self.facts:
                return
            rule_fact = self._get_fact(fact_or_rule)
            if not rule_fact:
                return
        if isinstance(rule_fact, Fact):
            if len(rule_fact.supported_by) >= 1:
                if not rule_fact.asserted:
                    return
                else:
                    rule_fact.asserted = False
                    return
            else:
                self.facts.remove(rule_fact)

        if isinstance(rule_fact, Rule):
            if rule_fact.asserted or len(rule_fact.supported_by) >= 1:
                return
            else:
                self.rules.remove(rule_fact)

        supported_r = rule_fact.supports_rules
        supported_f = rule_fact.supports_facts

        for item in supported_r:
            for rul in item.supported_by:
                if fact_or_rule in rul:
                    self._get_rule(item).supported_by.remove(rul)
            self.kb_retract(item)

        for item in supported_f:
            for fac in item.supported_by:
                if fact_or_rule in fac:
                    self._get_fact(item).supported_by.remove(fac)
            self.kb_retract(item)
        

class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here
        b_list = match(fact.statement, rule.lhs[0])
        support = [fact, rule]

        if (b_list):
            if len(rule.lhs) == 1:
                to_add = Fact(instantiate(rule.rhs, b_list))

                to_add.supported_by.append(support)
                to_add.asserted = False

                fact.supports_facts.append(to_add)
                rule.supports_facts.append(to_add)

                kb.kb_assert(to_add)

            else:
                left = []
                right = (instantiate(rule.rhs, b_list))

                for r in rule.lhs[1:]:
                    left.append(instantiate(r, b_list))

                to_add = Rule([left, right], [support])
                to_add.asserted = False

                fact.supports_rules.append(to_add)
                rule.supports_rules.append(to_add)

                kb.kb_assert(to_add)
