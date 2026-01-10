# tron-rust

> [!WARNING]
> Work in progress, implementation incomplete.
>
> The implementation work is being done on the [impl-2](https://github.com/oliverlambson/tron-rust/tree/impl-2) branch, check that out for progress in the meantime.

<picture>
  <img src="assets/logo.png" alt="TRON logo">
</picture>

Rust implementation of the [TRON](https://github.com/delaneyj/tron/tree/main) binary format, with Python bindings.

Goals:

1. Implement the TRON spec in Rust
   1. [x] xxhash32
   2. [ ] codec (scalar + tree)
      - [ ] decode - should read directly from underlying tron byte buffer (zero-copy, minimal allocations)
        - [x] values
        - [x] trailer
        - [ ] documents
      - [ ] encode - should mutate the underlying tron byte buffer
   3. [ ] copy on write update helper functions
   4. [ ] JMESPath queries
   5. [ ] JSON merge patch
   6. [ ] JSON schema validation
   7. [ ] Benchmarks vs. go impl
2. Implement python library with a pythonic API

```python
import tron

type TronType = (
  tron.Nil
  | tron.Bit
  | tron.I64
  | tron.F64
  | tron.Txt
  | tron.Bin
  | tron.Arr
  | tron.Map
)
def from_json(json: str) -> tron.TronType: ...

data = tron.from_json('{"name": "John Doe", "email": ["john@example.com", "jd@example.com"], "age": 42, "height": 183.5}')

# Types
reveal_type(data)             # Revealed type: `tron.Map`
reveal_type(data["name"])     # Revealed type: `tron.Txt`
reveal_type(data["email"])    # Revealed type: `tron.Arr`
reveal_type(data["email"][0]) # Revealed type: `tron.Txt`
reveal_type(data["age"])      # Revealed type: `tron.I64`
reveal_type(data["height"])   # Revealed type: `tron.F64`

# Familiar getting/setting on maps and arrays
name = data["name"]           # get key's value; same as `data.get("name")`
data["name"] = "Jimmy"        # update existing key's value; same as `data.set("name", "Jimmy")`
data["occupation"] = "Pilot"  # set new key/value pair; same as `data.set("occupation", "Pilot")`
del data["occupation"]        # delete key/value pair;  same as `data.delete("occupation")`
age = data.pop("age", 42)     # pop key/value pair (w/ optional default)
data.keys()                   # iterable of all map's keys
data.values()                 # iterable of all map's keys
data.items()                  # iterable of map's key/value pairs
len(data)                     # number key/value pairs in map; same as `data.??`
"height" in data              # check if key exists in map; same as `data.??`
data.update({"a": 1, "b": 2}) # merge new map into map
data.setdefault("level", 0)   # set value only if key doesn't exist in map
data.clear()                  # unset all key/value pairs in map

data["email"][0]                         # get arr element 0; same as `data["email"].get(0)`
data["email"][-1]                        # get arr's last element; same as `data["email"].get(-1)`
data["email"][1:3]                       # get slice of arr; same as `data["email"].get(1, 3)`
data["email"].append("john@doe.com")     # append new element to arr
data["email"].insert(0, "john@doe.com")  # append new element to arr
data["email"].extend(["a@e", "b@e"])     # append new elements to arr
e0 = data["email"].pop(0)                # pop value at index (default -1)
del data["email"][0]                     # delete value;  same as `data["email"].delete(0)`
data["email"].clear()                    # delete all values
# what about: index, count, sort, reverse?
...

# Methods on tron.Map
data.get("email")
...
```
