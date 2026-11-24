//! The pack reader takes bytes no repository vouches for (packages.fetching): a pack a server
//! sends, or one on the machine with its index. Corrupt or hostile bytes give an error, never a
//! crash, an allocation of the size a pack declares, or a loop.

use miniz_oxide::deflate::compress_to_vec_zlib;
use stilt_pkg::git::{Id, read_indexed, read_sent};

/// An object's header in a pack: its kind and its size, four bits then seven a byte.
fn header(kind: u8, mut size: usize) -> Vec<u8> {
    let mut out = vec![(kind << 4) | u8::try_from(size & 15).unwrap()];
    size >>= 4;
    while size > 0 {
        *out.last_mut().unwrap() |= 0x80;
        out.push(u8::try_from(size & 0x7f).unwrap());
        size >>= 7;
    }
    out
}

/// A whole object: its header and its bytes compressed.
fn whole(kind: u8, data: &[u8]) -> Vec<u8> {
    let mut out = header(kind, data.len());
    out.extend(compress_to_vec_zlib(data, 6));
    out
}

/// A pack holding `objects`, each already encoded.
fn pack(objects: &[Vec<u8>]) -> (Vec<u8>, Vec<usize>) {
    let mut out = b"PACK\0\0\0\x02".to_vec();
    out.extend(u32::try_from(objects.len()).unwrap().to_be_bytes());
    let mut offsets = Vec::new();
    for object in objects {
        offsets.push(out.len());
        out.extend(object);
    }
    out.extend([0; 20]);
    (out, offsets)
}

/// An index of version 2 listing `entries`, each an id and an offset.
fn index(entries: &[(Id, usize)]) -> Vec<u8> {
    let mut entries = entries.to_vec();
    entries.sort_unstable();
    let mut out = vec![0xff, b't', b'O', b'c', 0, 0, 0, 2];
    for byte in 0..=255u8 {
        let count = entries.iter().filter(|(id, _)| id[0] <= byte).count();
        out.extend(u32::try_from(count).unwrap().to_be_bytes());
    }
    for (id, _) in &entries {
        out.extend(id);
    }
    out.extend(vec![0; 4 * entries.len()]);
    for (_, offset) in &entries {
        out.extend(u32::try_from(*offset).unwrap().to_be_bytes());
    }
    out.extend([0; 40]);
    out
}

fn id(n: u8) -> Id {
    [n; 20]
}

/// A delta against the object `back` bytes before it, under 128, made of `ops`.
fn offset_delta(back: u8, ops: &[u8]) -> Vec<u8> {
    let mut out = header(6, ops.len());
    out.push(back);
    out.extend(compress_to_vec_zlib(ops, 6));
    out
}

#[test]
fn a_blob_and_a_delta_on_it_read() {
    let base = whole(3, b"hello");
    // The delta copies the base's five bytes, then inserts one.
    let delta = offset_delta(
        u8::try_from(base.len()).unwrap(),
        &[5, 6, 0x91, 0, 5, 1, b'!'],
    );
    let (data, offsets) = pack(&[base, delta]);
    assert_eq!(read_sent(&data), Ok(2));
    let index = index(&[(id(1), offsets[0]), (id(2), offsets[1])]);
    assert_eq!(read_indexed(index, data), Ok(2));
}

#[test]
fn a_declared_size_is_not_allocated() {
    let mut object = header(3, 1 << 29);
    object.extend(compress_to_vec_zlib(b"small", 6));
    assert!(read_sent(&pack(&[object]).0).is_err());
    let mut object = header(3, 1 << 40);
    object.extend(compress_to_vec_zlib(b"small", 6));
    assert!(read_sent(&pack(&[object]).0).is_err());
}

#[test]
fn a_delta_whose_base_is_itself_is_corrupt() {
    let (data, offsets) = pack(&[offset_delta(0, &[0, 0, 0])]);
    assert!(read_sent(&data).is_err());
    let index = index(&[(id(1), offsets[0])]);
    assert!(read_indexed(index, data).is_err());
}

#[test]
fn deltas_based_on_each_other_end() {
    let delta_on = |base: Id| {
        let mut object = header(7, 3);
        object.extend(base);
        object.extend(compress_to_vec_zlib(&[0, 0, 0], 6));
        object
    };
    let (data, offsets) = pack(&[delta_on(id(2)), delta_on(id(1))]);
    let index = index(&[(id(1), offsets[0]), (id(2), offsets[1])]);
    let error = read_indexed(index, data).unwrap_err();
    assert!(error.contains("deep"), "{error}");
}

#[test]
fn an_index_shorter_than_it_counts_is_refused() {
    let mut short = index(&[(id(1), 12)]);
    let count = 8 + 4 * 255;
    short[count..count + 4].copy_from_slice(&1000u32.to_be_bytes());
    assert!(read_indexed(short, pack(&[whole(3, b"x")]).0).is_err());
    assert!(read_indexed(vec![0xff, b't', b'O', b'c', 0, 0, 0, 2], Vec::new()).is_err());
}

#[test]
fn a_delta_writing_past_its_size_is_corrupt() {
    // The delta declares one byte, then inserts two.
    let ops = [5, 1, 2, b'a', b'b'];
    let base = whole(3, b"hello");
    let delta = offset_delta(u8::try_from(base.len()).unwrap(), &ops);
    assert!(read_sent(&pack(&[base, delta]).0).is_err());
}
