# Jupyter Note Book Integration

Other relevant files to consult in the repository:

- `theory_lib/jupyter/README_jupyter.md` documents the current jupyter notebook integration
- `theory_lib/README.md`
- `model_checker/README.md`

## TODOs

- [ ] revise `theory_lib/jupyter/jupyter_demo.ipynb` as needed to get its cells to run, looking at the `exclusion/examples.py` module for inspiration
- [ ] test `jupyter_demo.ipynb`, confirming that all cells are up and running

## Current problems to be solved in `jupyter_demo.ipynb`

Here is the sixth cell:

```
# Create an explorer with the default theory
explorer = InteractiveModelExplorer()

# Display the interactive UI
explorer.display()
```

I'm getting the following error upon running the cell:

```
---------------------------------------------------------------------------
StopIteration                             Traceback (most recent call last)
File /nix/store/bi8y3lx1593a2i7blq9dgpv4kvkl46di-python3-3.12.8-env/lib/python3.12/site-packages/ipywidgets/widgets/widget_selection.py:133, in findvalue(array, value, compare)
    132 try:
--> 133     return next(x for x in array if compare(x, value))
    134 except StopIteration:

StopIteration: 

During handling of the above exception, another exception occurred:

ValueError                                Traceback (most recent call last)
File /nix/store/bi8y3lx1593a2i7blq9dgpv4kvkl46di-python3-3.12.8-env/lib/python3.12/site-packages/ipywidgets/widgets/widget_selection.py:242, in _Selection._validate_value(self, proposal)
    241 try:
--> 242     return findvalue(self._options_values, value, self.equals) if value is not None else None
    243 except ValueError:

File /nix/store/bi8y3lx1593a2i7blq9dgpv4kvkl46di-python3-3.12.8-env/lib/python3.12/site-packages/ipywidgets/widgets/widget_selection.py:135, in findvalue(array, value, compare)
    134 except StopIteration:
--> 135     raise ValueError('%r not in array'%value)

ValueError: 'default' not in array

During handling of the above exception, another exception occurred:

TraitError                                Traceback (most recent call last)
Cell In[6], line 2
      1 # Create an explorer with the default theory
----> 2 explorer = InteractiveModelExplorer()
      4 # Display the interactive UI
      5 explorer.display()

File ~/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/jupyter.py:347, in InteractiveModelExplorer.__init__(self, theory_name)
    338 self.settings = {
    339     'N': 3,
    340     'max_time': 5,
   (...)
    344     'model': True  # Default to looking for a satisfying model
    345 }
    346 self.model = None
--> 347 self._build_ui()

File ~/Documents/Philosophy/Projects/ModelChecker/Code/src/model_checker/jupyter.py:370, in InteractiveModelExplorer._build_ui(self)
    367 self.settings_accordion = self._build_settings_ui()
    369 # Theory selector
--> 370 self.theory_selector = widgets.Dropdown(
    371     options=self._get_available_theories(),
    372     value=self.theory_name,
    373     description='Theory:',
    374     style={'description_width': 'initial'}
    375 )
    376 self.theory_selector.observe(self._on_theory_change, names='value')
    378 # Check button

File /nix/store/bi8y3lx1593a2i7blq9dgpv4kvkl46di-python3-3.12.8-env/lib/python3.12/site-packages/ipywidgets/widgets/widget_selection.py:186, in _Selection.__init__(self, *args, **kwargs)
    183     kwargs['index'] = 0 if nonempty else None
    184     kwargs['label'], kwargs['value'] = options[0] if nonempty else (None, None)
--> 186 super().__init__(*args, **kwargs)
    187 self._initializing_traits_ = False

File /nix/store/bi8y3lx1593a2i7blq9dgpv4kvkl46di-python3-3.12.8-env/lib/python3.12/site-packages/ipywidgets/widgets/widget_description.py:35, in DescriptionWidget.__init__(self, *args, **kwargs)
     33     kwargs.setdefault('tooltip', kwargs['description_tooltip'])
     34     del kwargs['description_tooltip']
---> 35 super().__init__(*args, **kwargs)

File /nix/store/bi8y3lx1593a2i7blq9dgpv4kvkl46di-python3-3.12.8-env/lib/python3.12/site-packages/ipywidgets/widgets/widget.py:503, in Widget.__init__(self, **kwargs)
    501 """Public constructor"""
    502 self._model_id = kwargs.pop('model_id', None)
--> 503 super().__init__(**kwargs)
    505 Widget._call_widget_constructed(self)
    506 self.open()

File /nix/store/bi8y3lx1593a2i7blq9dgpv4kvkl46di-python3-3.12.8-env/lib/python3.12/site-packages/traitlets/traitlets.py:1369, in HasTraits.__init__(self, *args, **kwargs)
   1367 changed = set(kwargs) & set(self._traits)
   1368 for key in changed:
-> 1369     value = self._traits[key]._cross_validate(self, getattr(self, key))
   1370     self.set_trait(key, value)
   1371     changes[key]["new"] = value

File /nix/store/bi8y3lx1593a2i7blq9dgpv4kvkl46di-python3-3.12.8-env/lib/python3.12/site-packages/traitlets/traitlets.py:730, in TraitType._cross_validate(self, obj, value)
    728 if self.name in obj._trait_validators:
    729     proposal = Bunch({"trait": self, "value": value, "owner": obj})
--> 730     value = obj._trait_validators[self.name](obj, proposal)
    731 elif hasattr(obj, "_%s_validate" % self.name):
    732     meth_name = "_%s_validate" % self.name

File /nix/store/bi8y3lx1593a2i7blq9dgpv4kvkl46di-python3-3.12.8-env/lib/python3.12/site-packages/traitlets/traitlets.py:1241, in EventHandler.__call__(self, *args, **kwargs)
   1239 """Pass `*args` and `**kwargs` to the handler's function if it exists."""
   1240 if hasattr(self, "func"):
-> 1241     return self.func(*args, **kwargs)
   1242 else:
   1243     return self._init_call(*args, **kwargs)

File /nix/store/bi8y3lx1593a2i7blq9dgpv4kvkl46di-python3-3.12.8-env/lib/python3.12/site-packages/ipywidgets/widgets/widget_selection.py:244, in _Selection._validate_value(self, proposal)
    242     return findvalue(self._options_values, value, self.equals) if value is not None else None
    243 except ValueError:
--> 244     raise TraitError('Invalid selection: value not found')

TraitError: Invalid selection: value not found
```

