# relation utilities


class EventS():
	id = 0
	datatype = None
	def __hash__(self):
		return hash(self.id)

# http://stackoverflow.com/questions/8673482/transitive-closure-python-tuples
# transitive-closure-python-tuples
def transitive_closure(a):
    closure = set(a)
    while True:
        new_relations = set((x,w) for x,y in closure for q,w in closure if q == y)

        closure_until_now = closure | new_relations

        if closure_until_now == closure:
            break

        closure = closure_until_now

    return closure

def concat_relation(a, b):
	a = set(a)
	b = set(b)
	new_relations = set((x,j)  for (x,y) in a for (i,j) in b if (y == i))
	return new_relations

if __name__ == '__main__':
	s = set([(1,2), (2,3)])
	sb = set([(3,5)])
	s = transitive_closure(s)
	print s
	print concat_relation(s, sb)

	print (1,4) in s