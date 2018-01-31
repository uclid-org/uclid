// Author: Emil Stefanov (emil@berkeley.edu)
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace SimplePathORamSample
{
	class Program
	{
		static void Main(string[] args)
		{
			SimplePathORamSimulator simulator = new SimplePathORamSimulator(13, 13, 4, new Random());

			Console.WriteLine("Blocks: 2^" + Math.Log(simulator.BlockCount, 2));

			long operationCount = simulator.BlockCount * 3;
			for (long i = 0; i < operationCount; i++)
				simulator.Access(simulator.Random.Next(simulator.BlockCount));

			Console.WriteLine("Max cache size: " + simulator.MaxCacheCount);
			Console.WriteLine();
		}
	}

	public class SimplePathORamSimulator
	{
		private class Block
		{
			public int Id;
			public int Position;
		}

		private List<Block> m_cache = new List<Block>();
		private Block[][] m_buckets;
		private int[] m_positions;

		public Random Random { get; private set; }
		public int BlockCount { get; private set; }
		public int LeafCount { get; private set; }
		public int LevelCount { get; private set; }
		public int MaxCacheCount { get; private set; }
		public int BlocksPerBucket { get; private set; }

		public SimplePathORamSimulator(int blockCountLog, int leafCountLog, int blocksPerBucket, Random random)
		{
			this.BlockCount = (1 << blockCountLog);
			this.LeafCount = (1 << leafCountLog);
			this.LevelCount = leafCountLog + 1;
			this.BlocksPerBucket = blocksPerBucket;
			this.Random = random;
			m_buckets = new Block[this.LeafCount * 2 - 1][];
			m_positions = new int[this.BlockCount];

			for (int i = 0; i < m_buckets.Length; i++)
				m_buckets[i] = new Block[this.BlocksPerBucket];

			// Initialize block placements.
			for (int blockId = 0; blockId < this.BlockCount; blockId++)
			{
				m_positions[blockId] = this.Random.Next(this.LeafCount);
				m_cache.Add(new Block { Id = blockId });
				Access(blockId);
			}
		}

		public void Access(int id)
		{
			// Remap block.
			int oldPosition = m_positions[id];
			int newPosition = this.Random.Next(this.LeafCount);
			m_positions[id] = newPosition;

			// Read path.
			int bucketIndex = this.LeafCount - 1 + oldPosition;
			while (true)
			{
				m_cache.AddRange(from block in m_buckets[bucketIndex] where block != null select block);

				if (bucketIndex == 0)
					break;

				bucketIndex = (bucketIndex - 1) / 2;
			}

			this.MaxCacheCount = Math.Max(this.MaxCacheCount, m_cache.Count);

			// Search cache.
			Block fetchedBlock = m_cache.Find(block => block.Id == id);
			fetchedBlock.Position = newPosition;

			// Sort cache.
			m_cache.Sort((block1, block2) => (block2.Position ^ oldPosition) - (block1.Position ^ oldPosition));

			// Write path.
			bucketIndex = this.LeafCount - 1 + oldPosition;
			for (int height = 0; height < this.LevelCount; height++)
			{
				Block[] bucket = m_buckets[bucketIndex];

				for (int i = 0; i < bucket.Length; i++)
				{
					Block block = m_cache.Count == 0 ? null : m_cache[m_cache.Count - 1];

					if (block != null && (block.Position >> height) == (oldPosition >> height))
						m_cache.RemoveAt(m_cache.Count - 1);
					else
						block = null;

					bucket[i] = block;
				}

				bucketIndex = (bucketIndex - 1) / 2;
			}
		}
	}
}
