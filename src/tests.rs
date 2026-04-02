/// Generate test cases that need internal access to fields
#[macro_export]
macro_rules! gen_tests_internal {
    ($vecdeq:tt) => {
        #[test]
        fn test_swap_front_back_remove() {
            fn test(back: bool) {
                // This test checks that every single combination of tail position and length is
                // tested. Capacity 15 should be large enough to cover every case.
                let mut tester = <$vecdeq<[_; 15]>>::new();
                let usable_cap = tester.capacity();
                let final_len = usable_cap / 2;

                for len in 0..final_len {
                    let mut expected = <$vecdeq<[_; 15]>>::new();
                    if back {
                        expected.extend(0..len)
                    } else {
                        expected.extend((0..len).rev())
                    };
                    for head_pos in 0..usable_cap {
                        tester.head = head_pos;
                        tester.len = 0;
                        if back {
                            for i in 0..len * 2 {
                                tester.push_front(i);
                            }
                            for i in 0..len {
                                assert_eq!(tester.swap_remove_back(i), Some(len * 2 - 1 - i));
                            }
                        } else {
                            for i in 0..len * 2 {
                                tester.push_back(i);
                            }
                            for i in 0..len {
                                let idx = tester.len() - 1 - i;
                                assert_eq!(tester.swap_remove_front(idx), Some(len * 2 - 1 - i));
                            }
                        }
                        assert!(tester.head <= tester.capacity());
                        assert!(tester.len <= tester.capacity());
                        assert_eq!(tester, expected);
                    }
                }
            }
            test(true);
            test(false);
        }

        #[test]
        fn test_insert() {
            // This test checks that every single combination of tail position, length, and
            // insertion position is tested. Capacity 15 should be large enough to cover
            // every case.

            let mut tester = <$vecdeq<[_; 15]>>::new();
            // can't guarantee we got 15, so have to get what we got.
            // 15 would be great, but we will definitely get 2^k - 1, for k >= 4, or else
            // this test isn't covering what it wants to
            let cap = tester.capacity();

            // len is the length *after* insertion
            let minlen = if cfg!(miri) { cap - 1 } else { 1 }; // Miri is too slow
            for len in minlen..cap {
                // 0, 1, 2, .., len - 1
                let mut expected = <$vecdeq<[_; 15]>>::new();
                expected.extend((0..).take(len));
                for head_pos in 0..cap {
                    for to_insert in 0..len {
                        tester.head = head_pos;
                        tester.len = 0;
                        for i in 0..len {
                            if i != to_insert {
                                tester.push_back(i);
                            }
                        }
                        tester.insert(to_insert, to_insert);
                        assert_eq!(tester, expected);
                    }
                }
            }
        }
        #[test]
        fn make_contiguous_big_head() {
            let mut tester = <$vecdeq<[_; 15]>>::new();

            for i in 0..3 {
                tester.push_back(i);
            }

            for i in 3..10 {
                tester.push_front(i);
            }

            // 012......9876543
            assert_eq!(tester.capacity(), 15);
            assert_eq!(
                (&[9, 8, 7, 6, 5, 4, 3] as &[_], &[0, 1, 2] as &[_]),
                tester.as_slices()
            );

            tester.make_contiguous();
            assert_eq!(tester.head, 0);
            assert_eq!(
                (&[9, 8, 7, 6, 5, 4, 3, 0, 1, 2] as &[_], &[] as &[_]),
                tester.as_slices()
            );
        }

        #[test]
        fn make_contiguous_big_tail() {
            let mut tester = <$vecdeq<[_; 15]>>::new();

            for i in 0..8 {
                tester.push_back(i);
            }

            for i in 8..10 {
                tester.push_front(i);
            }

            // 01234567......98
            tester.make_contiguous();
            assert_eq!(tester.head, 0);
            assert_eq!(
                (&[9, 8, 0, 1, 2, 3, 4, 5, 6, 7] as &[_], &[] as &[_]),
                tester.as_slices()
            );
        }

        #[test]
        fn make_contiguous_small_free() {
            let mut tester = <$vecdeq<[_; 16]>>::new();

            for i in b'A'..b'I' {
                tester.push_back(i as char);
            }

            for i in b'I'..b'N' {
                tester.push_front(i as char);
            }

            assert_eq!(tester, [
                'M', 'L', 'K', 'J', 'I', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H'
            ]);

            // ABCDEFGH...MLKJI
            tester.make_contiguous();
            assert_eq!(tester.head, 0);
            assert_eq!(
                (
                    &['M', 'L', 'K', 'J', 'I', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H'] as &[_],
                    &[] as &[_]
                ),
                tester.as_slices()
            );

            tester.clear();
            for i in b'I'..b'N' {
                tester.push_back(i as char);
            }

            for i in b'A'..b'I' {
                tester.push_front(i as char);
            }

            // IJKLM...HGFEDCBA
            tester.make_contiguous();
            assert_eq!(tester.head, 0);
            assert_eq!(
                (
                    &['H', 'G', 'F', 'E', 'D', 'C', 'B', 'A', 'I', 'J', 'K', 'L', 'M'] as &[_],
                    &[] as &[_]
                ),
                tester.as_slices()
            );
        }

        #[test]
        fn make_contiguous_head_to_end() {
            let mut tester = <$vecdeq<[_; 16]>>::new();

            for i in b'A'..b'L' {
                tester.push_back(i as char);
            }

            for i in b'L'..b'Q' {
                tester.push_front(i as char);
            }

            assert_eq!(tester, [
                'P', 'O', 'N', 'M', 'L', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K'
            ]);

            // ABCDEFGHIJKPONML
            tester.make_contiguous();
            assert_eq!(tester.head, 0);
            assert_eq!(
                (
                    &[
                        'P', 'O', 'N', 'M', 'L', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J',
                        'K'
                    ] as &[_],
                    &[] as &[_]
                ),
                tester.as_slices()
            );

            tester.clear();
            for i in b'L'..b'Q' {
                tester.push_back(i as char);
            }

            for i in b'A'..b'L' {
                tester.push_front(i as char);
            }

            // LMNOPKJIHGFEDCBA
            tester.make_contiguous();
            assert_eq!(tester.head, 0);
            assert_eq!(
                (
                    &[
                        'K', 'J', 'I', 'H', 'G', 'F', 'E', 'D', 'C', 'B', 'A', 'L', 'M', 'N', 'O',
                        'P'
                    ] as &[_],
                    &[] as &[_]
                ),
                tester.as_slices()
            );
        }

        #[test]
        fn test_remove() {
            // This test checks that every single combination of tail position, length, and
            // removal position is tested. Capacity 15 should be large enough to cover every
            // case.

            // can't guarantee we got 15, so have to get what we got.
            // 15 would be great, but we will definitely get 2^k - 1, for k >= 4, or else
            // this test isn't covering what it wants to
            const CAP: usize = 15;

            // len is the length *after* removal
            let minlen = if cfg!(miri) { CAP - 2 } else { 0 }; // Miri is too slow
            for len in minlen..CAP - 1 {
                // 0, 1, 2, .., len - 1
                let mut expected = <$vecdeq<[_; 15]>>::new();
                expected.extend((0..).take(len));
                for head_pos in 0..CAP {
                    for to_remove in 0..=len {
                        let mut tester = <$vecdeq<[_; CAP]>>::new();
                        tester.head = head_pos;
                        for i in 0..len {
                            if i == to_remove {
                                tester.push_back(1234);
                            }
                            tester.push_back(i);
                        }
                        if to_remove == len {
                            tester.push_back(1234);
                        }
                        tester.remove(to_remove);
                        assert!(tester.head <= tester.capacity());
                        assert!(tester.len <= tester.capacity());
                        assert_eq!(tester, expected);
                    }
                }
            }
        }
        #[test]
        fn test_range() {
            const CAP: usize = 7;
            let minlen = if cfg!(miri) { CAP - 1 } else { 0 }; // Miri is too slow
            for len in minlen..=CAP {
                for head in 0..CAP {
                    for start in 0..=len {
                        for end in start..=len {
                            let mut tester = <$vecdeq<[_; CAP]>>::new();
                            tester.head = head;
                            for i in 0..len {
                                tester.push_back(i);
                            }

                            // Check that we iterate over the correct values
                            let range: Vec<_> = tester.range(start..end).copied().collect();
                            let expected: Vec<_> = (start..end).collect();
                            assert_eq!(range, expected);
                        }
                    }
                }
            }
        }

        #[test]
        fn test_range_mut() {
            const CAP: usize = 7;

            for len in 0..=CAP {
                for head in 0..CAP {
                    for start in 0..=len {
                        for end in start..=len {
                            let mut tester = <$vecdeq<[_; CAP]>>::new();
                            tester.head = head;
                            for i in 0..len {
                                tester.push_back(i);
                            }

                            let head_was = tester.head;
                            let len_was = tester.len;

                            // Check that we iterate over the correct values
                            let range: Vec<_> = tester.range_mut(start..end).map(|v| *v).collect();
                            let expected: Vec<_> = (start..end).collect();
                            assert_eq!(range, expected);

                            // We shouldn't have changed the capacity or made the
                            // head or tail out of bounds
                            assert_eq!(tester.head, head_was);
                            assert_eq!(tester.len, len_was);
                        }
                    }
                }
            }
        }

        #[test]
        fn test_drain() {
            const CAP: usize = 7;

            for len in 0..=CAP {
                for head in 0..CAP {
                    for drain_start in 0..=len {
                        for drain_end in drain_start..=len {
                            let mut tester = <$vecdeq<[_; CAP]>>::new();
                            tester.head = head;
                            tester.len = 0;
                            for i in 0..len {
                                tester.push_back(i);
                            }

                            // Check that we drain the correct values
                            let drained: Vec<_> = tester.drain(drain_start..drain_end).collect();
                            let drained_expected: Vec<_> = (drain_start..drain_end).collect();
                            assert_eq!(drained, drained_expected);

                            // We shouldn't have changed the capacity or made the
                            // head or tail out of bounds
                            assert!(tester.head <= tester.capacity());
                            assert!(tester.len <= tester.capacity());

                            // We should see the correct values in the VecDeque
                            let expected: Vec<_> = (0..drain_start).chain(drain_end..len).collect();
                            assert_eq!(tester, expected, "{drain_start:?} {drain_end:?}");
                        }
                    }
                }
            }
        }
    };
}

#[macro_export]
macro_rules! gen_tests {
    ($vecdeq:tt) => {
        #[test]
        fn test_extend_drain() {
            let mut tester = <$vecdeq<[_; 6]>>::new();
            tester.extend([1, 2, 3, 4, 5, 6].into_iter().map(Box::new));

            {
                let mut it = tester.drain(3..5);
                assert_eq!(*it.next().unwrap(), 4);
            }

            let (head, tail) = tester.as_slices();
            assert_eq!(head.len(), 4);
            assert_eq!(*head[0], 1);
            assert_eq!(*head[1], 2);
            assert_eq!(*head[2], 3);
            assert_eq!(*head[3], 6);
            assert_eq!(tail, &[]);

            {
                let mut it = tester.drain(..2);
                assert_eq!(*it.next().unwrap(), 1);
            }
            let (head, tail) = tester.as_slices();
            assert_eq!(head.len(), 2);
            assert_eq!(*head[0], 3);
            assert_eq!(*head[1], 6);
            assert_eq!(tail, &[]);

            let mut tester = <$vecdeq<[_; 6]>>::new();
            tester.push_front(Box::new(1));
            tester.push_front(Box::new(2));
            tester.push_front(Box::new(3));
            tester.pop_back();
            tester.pop_back();
            tester.extend([1, 2, 3, 4, 5].into_iter().map(Box::new));
            {
                let mut it = tester.drain(3..5);
                assert_eq!(*it.next().unwrap(), 3);
            }
            let (head, tail) = tester.as_slices();
            assert_eq!(head.len(), 3);
            assert_eq!(*head[0], 3);
            assert_eq!(*head[1], 1);
            assert_eq!(*head[2], 2);
            assert_eq!(tail.len(), 1);
            assert_eq!(*tail[0], 5);
        }
        #[test]
        fn test_extend_from_slice() {
            let mut tester = <$vecdeq<[_; 5]>>::new();
            tester.extend_from_slice_copying(&[1, 2, 3]);
            assert_eq!(tester.len(), 3);

            assert_eq!(tester.get(0), Some(&1));
            assert_eq!(tester.get(1), Some(&2));
            assert_eq!(tester.get(2), Some(&3));
            assert_eq!(tester.get(3), None);

            tester.pop_back();
            tester.extend_from_slice_copying(&[1, 2]);

            let (head, tail) = tester.as_slices();
            assert_eq!(head, &[1, 2, 1, 2]);
            assert_eq!(tail, &[]);

            let mut tester = <$vecdeq<[_; 5]>>::new();
            tester.push_front(1);
            tester.push_front(2);
            tester.push_front(3);
            tester.pop_back();

            let (head, tail) = tester.as_slices();
            assert_eq!(head, &[3, 2]);
            assert_eq!(tail, &[]);

            tester.extend_from_slice_copying(&[1, 2, 3]);
            let (head, tail) = tester.as_slices();
            assert_eq!(head, &[3, 2, 1]);
            assert_eq!(tail, &[2, 3]);
        }
        #[test]
        fn test_get() {
            let mut tester = <$vecdeq<[_; 5]>>::new();
            tester.push_back(1);
            tester.push_back(2);
            tester.push_back(3);

            assert_eq!(tester.len(), 3);

            assert_eq!(tester.get(1), Some(&2));
            assert_eq!(tester.get(2), Some(&3));
            assert_eq!(tester.get(0), Some(&1));
            assert_eq!(tester.get(3), None);

            tester.remove(0);

            assert_eq!(tester.len(), 2);
            assert_eq!(tester.get(0), Some(&2));
            assert_eq!(tester.get(1), Some(&3));
            assert_eq!(tester.get(2), None);
        }
        #[test]
        fn test_get_mut() {
            let mut tester = <$vecdeq<[_; 3]>>::new();
            tester.push_back(1);
            tester.push_back(2);
            tester.push_back(3);

            assert_eq!(tester.len(), 3);

            if let Some(elem) = tester.get_mut(0) {
                assert_eq!(*elem, 1);
                *elem = 10;
            }

            if let Some(elem) = tester.get_mut(2) {
                assert_eq!(*elem, 3);
                *elem = 30;
            }

            assert_eq!(tester.get(0), Some(&10));
            assert_eq!(tester.get(2), Some(&30));
            assert_eq!(tester.get_mut(3), None);

            tester.remove(2);

            assert_eq!(tester.len(), 2);
            assert_eq!(tester.get(0), Some(&10));
            assert_eq!(tester.get(1), Some(&2));
            assert_eq!(tester.get(2), None);
        }

        #[test]
        fn test_swap() {
            let mut tester = <$vecdeq<[_; 3]>>::new();
            tester.push_back(1);
            tester.push_back(2);
            tester.push_back(3);

            assert_eq!(tester, [1, 2, 3]);

            tester.swap(0, 0);
            assert_eq!(tester, [1, 2, 3]);
            tester.swap(0, 1);
            assert_eq!(tester, [2, 1, 3]);
            tester.swap(2, 1);
            assert_eq!(tester, [2, 3, 1]);
            tester.swap(1, 2);
            assert_eq!(tester, [2, 1, 3]);
            tester.swap(0, 2);
            assert_eq!(tester, [3, 1, 2]);
            tester.swap(2, 2);
            assert_eq!(tester, [3, 1, 2]);
        }
        #[test]
        fn test_clone_from() {
            let m = vec![1; 8];
            let n = vec![2; 12];
            let limit = if cfg!(miri) { 4 } else { 8 }; // Miri is too slow
            for pfv in 0..limit {
                for pfu in 0..limit {
                    for longer in 0..2 {
                        let (vr, ur) = if longer == 0 { (&m, &n) } else { (&n, &m) };
                        let mut v = <$vecdeq<[_; 20]>>::new();
                        v.extend(vr.iter().copied());
                        for _ in 0..pfv {
                            v.push_front(1);
                        }
                        let mut u = <$vecdeq<[_; 20]>>::new();
                        u.extend(ur.iter().copied());
                        for _ in 0..pfu {
                            u.push_front(2);
                        }
                        v.clone_from(&u);
                        assert_eq!(&v, &u);
                    }
                }
            }
        }

        #[test]
        fn make_contiguous_head_to_end_2() {
            // Another test case for #79808, taken from #80293.

            let mut dq = <$vecdeq<[_; 16]>>::new();
            dq.extend(0..6);
            dq.pop_front();
            dq.pop_front();
            dq.push_back(6);
            dq.push_back(7);
            dq.push_back(8);
            dq.make_contiguous();
            let collected: Vec<_> = dq.iter().copied().collect();
            assert_eq!(dq.as_slices(), (&collected[..], &[] as &[_]));
        }

        #[test]
        #[should_panic = "assertion failed: b < self.len"]
        fn test_swap_panic() {
            let mut tester = <$vecdeq<[_; 3]>>::new();
            tester.push_back(1);
            tester.push_back(2);
            tester.push_back(3);
            tester.swap(2, 3);
        }

        #[test]
        fn test_retain() {
            let mut deq = ArrayVecDeq::<[_; 10]>::new();
            deq.extend(1..=10);
            deq.retain(|x| x & 1 == 0);
            let (head, tail) = deq.as_slices();
            assert_eq!(head, &[2, 4, 6, 8, 10]);
            assert_eq!(tail, &[]);

            let mut deq = ArrayVecDeq::<[_; 10]>::new();
            deq.extend((1..=10).map(Box::new));
            deq.retain(|x| (**x) & 1 == 0);

            let mut deq = ArrayVecDeq::<[_; 10]>::new();
            deq.extend(1..=10);
            deq.retain(|&x| x <= 5);
            let (head, tail) = deq.as_slices();
            assert_eq!(head, &[1, 2, 3, 4, 5]);
            assert_eq!(tail, &[]);

            let mut deq = ArrayVecDeq::<[_; 10]>::new();
            deq.extend(1..=10);
            deq.retain(|&x| x > 5);
            let (head, tail) = deq.as_slices();
            assert_eq!(head, &[6, 7, 8, 9, 10]);
            assert_eq!(tail, &[]);
        }
    };
}
