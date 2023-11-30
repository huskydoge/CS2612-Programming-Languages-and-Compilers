text = """
liveness(u)={#2,RAX}
liveness(u)={#5,#2}
liveness(u)={#5,#2,RAX}
liveness(u)={#5,#6,#2}
liveness(u)={#5,#6,#2,RAX}
liveness(u)={#5,#6,#2,#7}
liveness(u)={#5,#6,#2,#7,RAX}
liveness(u)={#5,#6,#2,#8,#7}
liveness(u)={#5,#6,#2,#8,#7}
liveness(u)={#0,#5,#6,#2,#8,#7}
liveness(u)={#5,#6,#2,#8,#7}
liveness(u)={#1,#5,#6,#2,#8,#7}
liveness(u)={#6,#2,#8,#9,#7,#5}
liveness(u)={#9,#10,#6,#2,#8,#5,#7}
liveness(u)={#3,#6,#2,#8,#5,#7}
liveness(u)={#3,#1,#6,#2,#8,#5,#7}
liveness(u)={#3,#11,#2,#5,#6,#8,#7}
liveness(u)={#3,#11,#12,#5,#6,#8,#7}
liveness(u)={#3,#4,#5,#6,#8,#7}
liveness(u)={#4,#1,#5,#6,#8,#7}
liveness(u)={#4,#5,#6,#8,#7}
liveness(u)={#5,#6,#2,#8,#7}
liveness(u)={#0,#5,#6,#2,#8,#7}
liveness(u)={#0,#5,#6,#2,#8,#7}
liveness(u)={#0,#5,#6,#2,#8,#7}
"""


sets = [line.split('=')[1].strip().strip('{}').split(',') for line in text.split('\n') if line]


elements_dict = {}

for s in sets:
    for element in s:
        if element not in elements_dict:
            elements_dict[element] = set()
        elements_dict[element].update(s)

# Remove each element from its own set
for element in elements_dict:
    elements_dict[element].remove(element)

# Defining the order for printing
order = [f"#{i}" for i in range(13)] + ["RAX"]

# turn sets into sorted lists
for element in elements_dict:
    elements_dict[element] = sorted(list(elements_dict[element]))
    


for element in order:
    if element in elements_dict:
        print(f"Element: {element}, Set: {elements_dict[element]}, Length: {len(elements_dict[element])}")
