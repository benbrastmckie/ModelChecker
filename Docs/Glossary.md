# Glossary

- This is a place to collect relevant commands, terms,... for reference.
- Entries should include a brief note as a reminder and any links to further information.
- Eventually I would like to turn this into a resources for others who are new to the project.
- For now, it is OK to use this as much or as little as is helpful.

## Z3

Bitwise operators: OR, AND,...

- OR is binary state-fusion and helps define state-parthood
- https://en.wikipedia.org/wiki/Bitwise_operation
- | (x | y) command is used for OR between bit vectors and returns a bvor (not sure how Z3 classifies this in terms of classes/primitive objects). This is different from the Or(x,y), which takes bools and returns a bool. 