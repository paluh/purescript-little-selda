# purescript-little-selda ... is dead!

## Long live the purescript-selda!

So just go directly to [purescript-selda](https://github.com/Kamirus/purescript-selda) !

This prototype was "literal port" of selda. It has nearly accomplished its mission as it had proven that we can use PureScript records to build queries and rows to represent tables.

It can rest in peace now.

Kamirus implementation is a complately new attempt with clear design and nicer API :-)

## About

An attempt to port Haskell Selda to Purescript. Pre-α stage.

It seems that I'm able to use wonderful purescript records instead of inductive tuples from original library - please check `test/Integration/Postgresql.purs` for details.

## Testing

```shell
$ pulp test --main 'Test.Integration'
```

## Progress of migration

- [x] Basic table representation
- [ ] Table/schema validation function (for postgresql)
- [x] Basic select from table
- [x] Restrict (`WHERE` clause)
- [x] Limit
- [x] Order
- [x] Left Join
- [x] Inner Join
- [x] Group by
- [x] Aggregation functions
- [x] Insert (prototype is specialized to postgresql with RETURNING)
- [ ] Delete
- [ ] Update
- [ ] Upsert
- [ ] Backend separation (currently all is tested against postgresql)
- [ ] Support for postgresql enums
