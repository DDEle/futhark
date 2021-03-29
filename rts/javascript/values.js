// Start of values.js
//
//


var type_strs = { "Int8Array" : '  i8',
              "Int16Array" : ' i16',
              "Int32Array" : ' i32',
              "BigInt64Array" : ' i64',
              "BigUint8Array" : '  u8',
              "BigUint16Array" :  ' u16',
              "BigUint32Array" :  ' u32',
              "BigUint64Array" :  ' u64',
              "Float32Array" : ' f32',
              "Float64Array" : ' f64',
              // TODO implement bool here
             };
var typToType = { '  i8' : Int8Array ,
              ' i16' : Int16Array ,
              ' i32' : Int32Array ,
              ' i64' : BigInt64Array ,
              '  u8' : Uint8Array ,
              ' u16' :  Uint16Array ,
              ' u32' :  Uint32Array ,
              ' u64' :  BigUint64Array ,
              ' f32' : Float32Array ,
              ' f64' : Float64Array ,
              // TODO implement bool here
             };

function binToStringArray(buff, array) {
  for (var i = 0; i < array.length; i++) {
    array[i] = buff[i];
  }
}

function fileToBuff(fname) {
  var readline = require('readline');
  var fs = require('fs');
  // TODO set decoding flag so there is no wack byte reading
  var buff =  fs.readFileSync(fname);
  return buff;
}

function fileToValue(fname) {
  var str = fileToBuff(fname);
  return read_binary(str);
}

function read_binary(buff) {
  // TODO Trim white space at the beggining
  //var buff = buff.trimStart();
  while (buff.slice(0, 1).toString().trim() == "") {
    buff = buff.slice(1);
  }
  if (buff[0] != 'b'.charCodeAt(0)) {
    throw "Not in binary format"
  }
  var version = buff[1];
  if (version != 2) {
    throw "Not version 2";
  }
  var num_dim = buff[2];
  var typ = buff.slice(3, 7);
  buff = buff.slice(7);
  if (num_dim == 0) {
    return read_bin_scalar(buff, typ);
  } else {
    return read_bin_array(buff, num_dim, typ);
  }
}

function read_bin_array(buff, num_dim, typ) {
  console.log("not implemented yet");
  return undefined;
}

var typToSize = {
  "bool" : 1,
  "  u8" : 1,
  "  i8" : 1,
  " u16" : 2,
  " i16" : 2,
  " u32" : 4,
  " i32" : 4,
  " f32" : 4,
  " u64" : 8,
  " i64" : 8,
  " f64" : 8,
}


function read_bin_scalar(buff, typ) {
  var size = typToSize[typ];
  var u8_array = new Uint8Array(size);
  binToStringArray(buff, u8_array);
  array = new (typToType[typ])(u8_array.buffer);
  return array[0];
}

  


function construct_binary_value(v) {

  var bytes = v.bytes_per_elem();
  var shape = v.shape();
  var values = v.values();
  var elems = 1;
  for (var i = 0; i < shape.length; i++) {
    elems = elems * Number(shape[i]);
  }
  var num_bytes = 1 + 1 + 1 + 4 + shape.length * 8 + elems * bytes;


  var bytes = new Uint8Array(num_bytes);
  bytes[0] = Buffer.from('b').readUInt8();
  bytes[1] = 2; // Not sure why this
  bytes[2] = shape.length

  var ftype = type_strs[v.str_type()];

  for (var i = 0; i < 4; i++) {
    bytes[3+i] = ftype.charCodeAt(i);
  }

  var sizes = new BigInt64Array(shape);
  var size_bytes = new Uint8Array(sizes.buffer);
  bytes.set(size_bytes, 7);

  var val_bytes = new Uint8Array(values.buffer);
  bytes.set(val_bytes, 7 + (shape.length * 8));
  
  return bytes;
}
