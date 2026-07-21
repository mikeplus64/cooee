{
  lib ? (import <nixpkgs> {}).lib,
  debug ? false,
}: let
  inherit
    (builtins)
    length
    elemAt
    filter
    foldl'
    isAttrs
    isBool
    isFloat
    isInt
    isList
    isPath
    isFunction
    isString
    listToAttrs
    match
    tryEval
    typeOf
    seq
    ;
  inherit (lib) pipe mapAttrs nameValuePair flip recursiveUpdate;
  inherit (lib.lists) imap0 foldr;
  inherit (lib.attrsets) concatMapAttrs attrsToList;
  inherit (lib.strings) concatMapAttrsStringSep concatMapStringsSep;
  inherit (lib.generators) toPretty;

  prettyValue = toPretty {
    allowPrettyValues = true;
    multiline = true;
    indent = "  ";
  };

  p = toPretty {
    allowPrettyValues = true;
    multiline = false;
    indent = "";
  };

  prettyTypeError = let
    pretty = indent:
      toPretty {
        allowPrettyValues = true;
        multiline = true;
        inherit indent;
      };
    go = indent: t:
      if isString t
      then "${indent}- ${t}"
      else if isAttrs t
      then
        concatMapAttrsStringSep "\n"
        (
          ctx: err:
            if isAttrs err
            then "${indent}${ctx}:\n${go "${indent}  " err}"
            else if isString err
            then "${indent}- ${ctx}: ${err}"
            else "${indent}- ${ctx}: ${pretty indent err}"
        )
        t
      else pretty indent t;
  in
    if debug
    then tyname: value: err: prettyValue {inherit tyname value err;}
    else tyname: value: err: "Type error while validating type (${tyname}) against value ${pretty "" value}:\n${go "" err}";

  /**
  Results are either:
  - Result.Ok (empty attrset)
  - Result.Err (non-empty attrset of "errors")
  */
  Result = rec {
    Ok = {};
    Err = name: error: {${name} = error;};
    isOk = x: isAttrs x && x == {};
    isErr = x: !(isOk x);

    fromVerifyFn = verifyFn: x: name: let
      result = tryEval (verifyFn x);
    in
      if result.success
      then
        if isBool result.value
        then
          if result.value
          then Ok
          else
            Err name {
              "got type" = typeOf x;
              "got value" =
                toPretty {
                  allowPrettyValues = true;
                  multiline = false;
                  indent = "";
                }
                x;
            }
        else wrap name result.value
      else
        Err name {
          "error while performing verification" = result.value;
        };

    case = x: {
      Ok,
      Err,
    }:
      if isOk x
      then Ok
      else Err;

    or = a: b:
      if isOk a
      then Ok
      else b;

    and = a: b:
      if isErr a
      then a
      else b;

    all = foldl' and Ok;
    any = inputs: foldr or (foldl' recursiveUpdate Ok inputs) inputs;
    wrap = name: e:
      if isOk e
      then Ok
      else Err name e;
  };

  /**
  Check if a value is a type

  The 'verify' function cannot really be verified in the design of this library
  so there are still oppourtunities unfortunately to get cryptic type error
  messages. It would have to be structured data that ultimately gets
  _interpretted_ by the 'verify' function instead of nested function calls.
  */
  isType = t:
    isAttrs t && t ? name && t ? verify && isFunction t.verify;

  /**
  The type all things narrow from
  */
  Any = {
    name = "";
    verify = _name: _: Result.Ok;
    __functor = expect;
  };

  /**
  The type of types - anything that satisfies 'isType'
  */
  type = __narrow Any {
    name = "type";
    verify = isType;
  };

  implies = cond: x: !cond || x;

  __narrow = super: spec:
    assert (isType super);
    assert (implies (spec ? name) (isString spec.name));
    assert (spec ? verify && isFunction spec.verify); {
      name =
        if spec ? name && isString spec.name
        then
          if super.name == ""
          then spec.name
          else "${super.name}.${spec.name}"
        else super.name;

      verify = name: x:
        Result.and
        (super.verify super.name x)
        (Result.fromVerifyFn spec.verify x name);

      __functor = expect;
    };

  /**
  Run a type check; returns Result.Ok if ok
  */
  verify = ty: ty.verify ty.name;

  /**
  Make a type out of any literal value; inputs to the type must be equal to the value
  */
  from = lambda compound (value:
    typedef {
      name = "from ${p value}";
      verify = x: x == value;
    });

  /**
  A type from a list of possible literals
  */
  enum = lambda (list.of compound) (ts: union (map from ts));

  /**
  Give a type an alias. Useful for breaking recursive types
  */
  alias = name: ty:
    assert (isString name); {
      inherit name;
      verify = _: value: ty.verify name value;
      __functor = expect;
    };

  expect = type: value:
    assert (isType type);
    assert (typeCheck type value); value;

  typeCheck = type: value: let
    result = verify type value;
  in
    assert (lib.trace "typeCheck ${p type} ${p value} = ${p result}" true);
      lib.asserts.assertMsg (Result.isOk result) (prettyTypeError type.name value result);

  isScalar = x:
    isPath x
    || isString x
    || isInt x
    || isFloat x
    || isBool x
    || x == null;

  /**
  Require the argument to a lambda be of a certain type
  */
  lambda = argType: typedFn: arg:
    seq (expect argType arg) (typedFn arg);

  /**
  Type for any "scalar" value i.e.
  - paths
  - strings
  - ints
  - floats
  - bools
  - null
  */
  scalar =
    __narrow Any {
      name = "scalar";
      verify = isScalar;
    }
    // {
      inherit int str bool path null_;
    };

  /**
  Type for any "compound" value, i.e. scalars, lists of scalars, or attrs of scalars.
  */
  compound = alias "compound" (union [
    scalar
    (list.of compound)
    (attrs.of compound)
  ]);

  null_ = __narrow Any {
    name = "null";
    verify = x: x == null;
  };

  bool = __narrow Any {
    name = "bool";
    verify = isBool;
  };

  path = __narrow Any {
    name = "path";
    verify = isPath;
  };

  str =
    __narrow Any {
      name = "str";
      verify = isString;
    }
    // {
      matching = lambda str (
        regex:
          __narrow str {
            name = "matches \"${regex}\"";
            verify = x: match regex x != null;
          }
      );
    };

  int = let
    base = __narrow Any {
      name = "int";
      verify = isInt;
    };
    subtype = name: verify: __narrow base {inherit name verify;};
    subtype1 = name: verify: n:
      __narrow base {
        name = "${name} ${toString n}";
        verify = verify n;
      };
    subtype2 = name: verify: n: m:
      __narrow base {
        name = "${name} ${toString n} ${toString m}";
        verify = verify n m;
      };
  in
    base
    // mapAttrs subtype {
      even = n: n == (n / 2) * 2;
      odd = n: n != (n / 2) * 2;
      positive = n: n > 0;
      natural = n: n >= 0;
    }
    // mapAttrs subtype1 {
      lt = n: x: x < n;
      gt = n: x: x > n;
      gte = n: x: x >= n;
      lte = n: x: x <= n;
    }
    // mapAttrs subtype2 {
      between = n: m: x: n <= x && x <= m;
    };

  float = let
    base = __narrow Any {
      name = "float";
      verify = isFloat;
    };
    subtype = name: verify: __narrow base {inherit name verify;};
    subtype1 = name: verify: n:
      __narrow base {
        name = "${name} ${toString n}";
        verify = verify n;
      };
    subtype2 = name: verify: n: m:
      __narrow base {
        name = "${name} ${toString n} ${toString m}";
        verify = verify n m;
      };
  in
    base
    // mapAttrs subtype {
      positive = n: n > 0.0;
      natural = n: n >= 0.0;
    }
    // mapAttrs subtype1 {
      lt = n: x: x < n;
      gt = n: x: x > n;
      gte = n: x: x >= n;
      lte = n: x: x <= n;
    }
    // mapAttrs subtype2 {
      between = n: m: x: n <= x && x <= m;
    };

  list =
    __narrow Any {
      name = "list";
      verify = isList;
    }
    // {
      sized = lambda int (size:
        __narrow list {
          name = "sized ${toString size}";
          verify = v: length v == size;
        });
      of = lambda type (t:
        __narrow list {
          name = "of (${t.name})";
          verify = flip pipe [
            (imap0 (i: x: nameValuePair "elemAt _ ${toString i}" (verify t x)))
            (filter (t: !(Result.isOk t.value))) # doesn't actually do anything
            listToAttrs
          ];
        });
    };

  attrs =
    __narrow Any {
      name = "attrs";
      verify = isAttrs;
    }
    // {
      of = lambda type (t:
        __narrow attrs {
          name = "of (${t.name})";
          verify = concatMapAttrs (
            key: type:
              Result.wrap "attr ${key}" (verify t type)
          );
        });
    };

  tuple = lambda (list.of type) (fieldTypes:
    __narrow (list.sized (length fieldTypes)) {
      name = "tuple [${concatMapStringsSep " " (t: t.name) fieldTypes}]";
      verify = value:
        Result.all (imap0 (i: t:
          if i < length value
          then verify t (elemAt value i)
          else Result.Err "elemAt _ ${toString i}" "Missing field")
        fieldTypes);
    });

  partial = lambda (attrs.of type) (fieldTypes:
    __narrow attrs {
      alias =
        if fieldTypes == {}
        then "partial {}"
        else "partial {${concatMapAttrsStringSep ";" (key: ty: "${key} = ${ty.name}") fieldTypes};}";
      verify = value:
        concatMapAttrs (
          key: type:
            if value ? ${key}
            then Result.wrap key (verify type value.${key})
            else Result.Ok
        )
        fieldTypes;
    });

  record = lambda (attrs.of type) (fieldTypes:
    __narrow attrs {
      name =
        if fieldTypes == {}
        then "record {}"
        else "record {${concatMapAttrsStringSep ";" (key: ty: "${key} = ${ty.name}") fieldTypes};}";
      verify = value:
        concatMapAttrs (
          key: type:
            if value ? ${key}
            then Result.wrap key (verify type value.${key})
            else Result.Err key "Missing field"
        )
        fieldTypes;
    });

  record' = lambda (attrs.of type) (fieldTypes:
    __narrow (record fieldTypes) {
      name =
        if fieldTypes == {}
        then "record' {}"
        else "record' {${concatMapAttrsStringSep ";" (key: ty: "${key} = ${ty.name}") fieldTypes};}";
      verify = value:
        Result.all
        (
          map
          ({name, ...}:
            if fieldTypes ? ${name}
            then Result.Ok
            else Result.Err name "Invalid field")
          (attrsToList value)
        );
    });

  union = lambda (list.of type) (types:
    __narrow Any {
      name = "union [${concatMapStringsSep " " (t: "(${t.name})") types}]";
      verify = value: Result.any (map (t: verify t value) types);
    });

  intersection = lambda (list.of type) (types:
    __narrow Any {
      name = "intersection [${concatMapStringsSep " " (t: t.name) types}]";
      verify = value: Result.all (map (t: verify t value) types);
    });

  function = __narrow Any {
    name = "function";
    verify = isFunction;
  };

  narrow = t: spec:
    __narrow (type t) (record' {
        name = str;
        verify = function;
      }
      spec);

  typedef = narrow Any;
in {
  inherit
    Result
    verify
    typedef
    narrow
    from
    enum
    alias
    intersection
    union
    record
    record'
    partial
    tuple
    attrs
    list
    float
    int
    str
    path
    bool
    null_
    compound
    scalar
    lambda
    ;
}
