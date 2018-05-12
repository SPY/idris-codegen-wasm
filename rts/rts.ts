/// <reference path="webassembly.d.ts" />

function loadIdris(bytes: BufferSource): Promise<any> {
    const mem = new WebAssembly.Memory({ initial: 10 })

    let buffer = new DataView(mem.buffer)

    const heap = {
        start: 0,
        next: 0,
        end: 0,
        size: 0,
        grow: 0
    }

    const stack = {
        bottom: 0,
        base: 0,
        top: 0
    }

    let retReg: number
    let tempReg: number

    function runGC() {

    }

    function aligned(size) {
        return (size + 3) & 0xFFFFFFFC
    }

    function allocate(size: number): number {
        const alignedSize = aligned(size)
        if (heap.next + alignedSize <= heap.end) {
            const addr = heap.next
            heap.next += alignedSize
            return addr
        }
        else {
            runGC()
            return allocate(size)
        }
    }

    return WebAssembly.instantiate(bytes, {
        rts: {
            allocate
        }
    })
}
